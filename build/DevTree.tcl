source [file join [file dirname [info script]] "scripts" "dts" "packed_item.tcl"]
source [file join [file dirname [info script]] "scripts" "dts" "ndp_header.tcl"]

# ----------------------------------------------------------------------

# Internal proc - creates VHDL package file from input hex string
proc DevTreeCreateVhd { DTV_PATH DTB_LIST } {
    set DTV_FILE [open $DTV_PATH w]
    puts $DTV_FILE "library IEEE;
use IEEE.std_logic_1164.all;

package dtb_pkg is
"
    foreach LI $DTB_LIST {
        lassign $LI DTB_SIZE DTB_VECTOR DTB_NAME
        puts $DTV_FILE "    constant ${DTB_NAME}_DATA : std_logic_vector(8*$DTB_SIZE-1 downto 0) := X\"$DTB_VECTOR\";\n"
    }
    puts $DTV_FILE "
end package dtb_pkg;

package body dtb_pkg is
end dtb_pkg;
"
    close $DTV_FILE
}

# ---------------------- Assemble Device Tree --------------------------
proc DevTreeBuildString { } {
   puts "Preparing for Device Tree build."

    global SYNTH_FLAGS

    set TOOL "vivado"
    if {[info exists SYNTH_FLAGS(TOOL)]} {
        set TOOL $SYNTH_FLAGS(TOOL)
    }

    if {$TOOL == "vivado"} {
        set BUILD_TOOL_COMMAND "vivado -version 2>/dev/null | grep Vivado | head -n1"
    } elseif {$TOOL == "quartus"} {
        set BUILD_TOOL_COMMAND "quartus_sh --tcl_eval puts {Quartus \\\$quartus(version)}"
    }

   # Get common build information
   if {[catch {exec {*}$BUILD_TOOL_COMMAND} BUILD_TOOL]} {
     set BUILD_TOOL_LINE   ""
   } else {
     set BUILD_TOOL_LINE   "build-tool      = \"$BUILD_TOOL\";"
   }

   if {[catch {exec git log -n1 --pretty=%h} BUILD_REVISION]} {
	   set BUILD_REVISION_LINE ""
   } else {
	   set BUILD_REVISION_LINE "build-revision  = \"$BUILD_REVISION\";"
   }
   if {[catch {exec git config user.email} BUILD_AUTHOR]} {
	   set BUILD_AUTHOR_LINE ""
   } else {
	   set BUILD_AUTHOR_LINE   "build-author    = \"$BUILD_AUTHOR\";"
   }
   catch {clock seconds} BUILD_TIME

   # check if function dts_build_netcope exists
   if { [llength [info procs dts_build_project]] > 0 } {
      set DTS_NETCOPE [dts_build_project]
   } else {
      set DTS_NETCOPE " "
   }

   # Fill bone string
   set DTS_STRING "/dts-v1/;
/ {
firmware {
   $BUILD_TOOL_LINE
   $BUILD_AUTHOR_LINE
   $BUILD_REVISION_LINE
   build-time      =  <$BUILD_TIME>;

   $DTS_NETCOPE
   };
};"

   return $DTS_STRING
}

# ----------------------------------------------------------------------

proc DevTreeGenerateBlob { PATH DTS_STRING {FILENAME "DevTree"} } {
    if {$DTS_STRING == ""} {
        return [list 0 ""]
    }

   # Set path variables
   set DTS_PATH $PATH.dts
   set DTB_PATH $PATH.dtb

   # Write string to Device Tree source file
   set DTS_FILE [open $DTS_PATH w]
   puts $DTS_FILE $DTS_STRING
   close $DTS_FILE


   puts "Building Device Tree. Source file will be stored in $DTS_PATH"

   # Check for errors & beautify Device Tree source
   # Old version of DTC writes something to stderr, even if the result code = 0
   set status 0
   if { [catch { exec dtc -I dts -O dts -o $DTS_PATH $DTS_PATH } msg ] } {
        if { [lindex $::errorCode 0] eq "CHILDSTATUS"} {
            set status [lindex $msg 2]
        } else {
        }
        if { $status != 0 } {
            puts stderr "Device Tree build failed!!!"
            puts stderr "Error status is: $::errorInfo"
            puts stderr $msg
            exit 1
        }
   }

   # 1. create Device Tree Blob with DTC compiler
   # 2. compress blob by xz
   # 3. convert archive to hex string with xxd (one line for each byte)
   # 4. revert the lines (tac) and concatenate back to one line (tr)
   # 5. fill prepared VHDL package skeleton with DTB vector

   catch {exec dtc -I dts -O dtb -o $DTB_PATH $DTS_PATH } msg
   exec xz -fk --check crc32 $DTB_PATH
   catch {exec stat --printf=%s $DTB_PATH.xz} DTB_SIZE
   catch {exec xxd -p -c 1 $DTB_PATH.xz | tac | tr -d " \n"} DTB_VECTOR

    file delete $DTB_PATH.xz

    puts "Device Tree successfully built."
    return [list $DTB_SIZE $DTB_VECTOR]
}

# ----------------------------------------------------------------------

proc DevTreeBuild { PATH } {
    puts "Phase for sourcing all Device Tree tcl scripts!"
    set dt_paths [open "DevTree_paths.txt" "r"]
    set sources [read $dt_paths]
    foreach i $sources {
        source $i
    }

    # Check presence of the Device Tree Compiler binary
    if { [catch {exec which dtc} msg] } {
        puts stderr "ERROR: Device Tree Compiler (dtc binary) not found!!!"
        puts stderr "       Please install dtc/libfdt package or build from source https://github.com/dgibson/dtc"
        exit 1
    }

    puts "Building Device Tree string!"
    set DTS_PF0_STRING [DevTreeBuildString]

    set DTS_VF0_STRING ""
    if { [llength [info procs dts_build_project_vf]] > 0 } {
        set DTS_VF0_STRING [dts_build_project_vf]
        if {$DTS_VF0_STRING != ""} {
            set DTS_VF0_STRING "/dts-v1/;/ {firmware {$DTS_VF0_STRING};};"
        }
    }

    lappend DTB_LIST [concat [DevTreeGenerateBlob "[file rootname $PATH]"   $DTS_PF0_STRING "DevTree"] "DTB_PF0"]
    lappend DTB_LIST [concat [DevTreeGenerateBlob "[file rootname $PATH]VF" $DTS_VF0_STRING "DevTreeVF"] "DTB_VF0"]
    DevTreeCreateVhd $PATH $DTB_LIST
}

proc nb_generate_file_register_devtree {{DT_PATH ""}} {
    if {$DT_PATH == ""} {
        global env
        set DT_PATH $env(NETCOPE_TEMP)DevTree.vhd
    }
    global SYNTH_FLAGS

    lappend SYNTH_FLAGS(NFW_FILES) [list [file rootname $DT_PATH].dts DevTree.dts]
    lappend SYNTH_FLAGS(NFW_FILES) [list [file rootname $DT_PATH].dtb DevTree.dtb]
    return [nb_generate_file_register $DT_PATH DevTreeBuild $DT_PATH "" "phony"]
}
