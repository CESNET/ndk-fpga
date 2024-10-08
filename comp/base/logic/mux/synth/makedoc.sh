#!/bin/bash

# Script for automatic testing of compenents for documentation purposes
# Script is based on "bparser", here comes original header:
# (script downloaded from:
#     http://linuxfromscratch.org/pipermail/alfs-discuss/2006-January/007537.html )

# Hint found later:
# Strip XML comments:
#sed -ne '/<!--/ { :c; /-->/! { N; b c; }; /-->/s/<!--.*-->//g }; /^  *$/!p;'

# Known problems:
# Script expects frequency 125 MHz (or period 8) in testing scripts

# project	:	a possible add-in for jhlfs?
# name		:	bparser
# version	:	0.7e (JAN2606)
# author	:	George Makrydakis <gmakmail at gmail.com>
# license	:	GPL v 2.x or up
# info		:	bash - based XML pseudoparser for the jhLFS Project
# status	:	any valid XML document can be parsed by this script, just substitute the myfile variable

# The testing script is written in the cycle at the end if the original parser
# Author: tnovot@liberouter.org

declare -a xmlSTAT				# contains the status informer
declare -a xmlDATA				# contains any relevant data (element/attributes name/values and unparsed data)
declare -i xINDEX=0				# global xINDEX pointer for xml**** arrays
declare -i checkpoint=0				# a character counter & pointer for parserLINE
declare -i doall=0				# a simple counter variable
declare -r myfile="synthesis.xml"	# the filename / path of the file to "parse"

declare -r startTAG='<'			# literal <
declare -r closeTAG='>'			# literal >
declare -r slashTAG='/'			# literal /
declare -r equalTAG='='			# literal =
declare -r quoteTAG='"'			# literal "
declare -r whiteTAG=' '			# literal
declare elmentATTN=""			# element attribute name
declare elmentATTV=""			# element attribute value
declare elmentNAME=""			# element name value
declare elmentDUMP=""			# element name dump

declare parserLINE=""			# contains a single line read from the XML document sent to the parser
declare parserFLAG="ENABLED"		# can have two mutually exclusive values: ENABLED / DISABLD
declare parserFILE=""			# file sent to the parser
declare parserBUFF=""			# parser buffer variable

while read parserLINE
   do
      parserBUFF=""
      for ((checkpoint=0; checkpoint < ${#parserLINE}; checkpoint++)) ;
      do
         case ${parserLINE:$checkpoint:1} in
            $startTAG)
               let "checkpoint++"; elmentNAME=""; parserFLAG="ENABLED"
               if [ "$parserBUFF" != '' ] ; then
                  xmlSTAT[xINDEX]="#"
                  xmlDATA[xINDEX]="$parserBUFF"
                  let "xINDEX++"
                  parserBUFF=""
               fi
               until [ "${parserLINE:$checkpoint:1}" = ' ' ] || \
                  [ "${parserLINE:$checkpoint:1}" = '>' ] || \
                  [ $checkpoint = ${#parserLINE} ];
               do
                  elmentNAME=$elmentNAME${parserLINE:$checkpoint:1}
                  let "checkpoint++"
               done
               if [ "${elmentNAME:0:1}" = "$slashTAG" ] ; then
                  xmlDATA[xINDEX]="${elmentNAME#*/}"
                  xmlSTAT[xINDEX]="$closeTAG"
                  let "xINDEX++"
                  parserBUFF=""
               else
                  xmlDATA[xINDEX]="$elmentNAME"
                  xmlSTAT[xINDEX]="$startTAG"
                  let "xINDEX++"; parserBUFF=""
                  case ${parserLINE:$checkpoint:1} in
                     $whiteTAG)	elmentDUMP="$elmentNAME" ;;
                     '')			elmentDUMP="$elmentNAME" ;;
                  esac
               fi
               ;;
            $slashTAG)
               case $parserFLAG in
                  ENABLED)
                     if [ "${parserLINE:$((checkpoint + 1)):1}" = "$closeTAG" ] ; then
                        xmlSTAT[xINDEX]="$closeTAG"
                        xmlDATA[xINDEX]="$elmentDUMP"
                        let "xINDEX++"
                        elmentDUMP=""; parserBUFF=""; let "checkpoint+=2"
                     fi
                     ;;
                  DISABLD)
                     ;;
               esac
               ;;
            $quoteTAG)
               case $parserFLAG in
                  ENABLED)
                     let "checkpoint++"; elmentATTV=""; parserBUFF=""
                     until [ "${parserLINE:$checkpoint:1}" = '"' ] ;
                     do
                        elmentATTV=$elmentATTV${parserLINE:$checkpoint:1}
                        let "checkpoint++"
                     done
                     let "checkpoint++"; xmlDATA[xINDEX]="$elmentATTV"; let "xINDEX++"
                        case ${parserLINE:$checkpoint:1} in
                           $closeTAG) if [ "${parserLINE:$((checkpoint + 1)):1}" = '<' ] ; then let "checkpoint-=1"; fi ;;
                           $slashTAG) let "checkpoint-=1" ;;
                        esac
                     ;;
                  DISABLD)
                     ;;
               esac
               ;;
            $equalTAG)
               case $parserFLAG in
                  ENABLED)
                     elmentATTN=""
                     if [ ${parserLINE:$((checkpoint + 1)):1} = '"' ] ; then
                        elmentATTN=${parserBUFF##$equalTAG}
                        elmentATTN=${elmentATTN##*$whiteTAG}
                        xmlSTAT[xINDEX]="$elmentATTN"
                     fi
                     ;;
                  DISABLD)
                     ;;
               esac
               ;;
         esac

         case $((checkpoint + 1)) in
            ${#parserLINE})
               parserBUFF=$parserBUFF${parserLINE:$checkpoint:1}
               if [ "${parserLINE:$checkpoint:1}" != "$closeTAG" ] ; then
                  xmlSTAT[xINDEX]="#"
                  xmlDATA[xINDEX]="$parserBUFF"
                  let "xINDEX++"
               fi
               ;;
            *)
               case ${parserLINE:$checkpoint:1} in
                  $closeTAG)	parserBUFF=""; parserFLAG="DISABLD";;
                  *)			parserBUFF=$parserBUFF${parserLINE:$checkpoint:1};;
               esac
               ;;
         esac

   done
done < "$myfile"

#########################################################################################

declare -i backup=0

# Display a formatted error message on the standard error output.
err () {
   if [ $backup -eq 1 ]; then
      # Restore the original file and scripts
      mv ../$toplevel.orig ../$toplevel
      mv XST.tcl.orig XST.tcl
      mv Precision.tcl.orig Precision.tcl
   fi
   echo ${0}: ${*} >&2
   exit 1
}

# Display warning
warn () {
   echo "Warning: ${*}" >&2
}

perform_test() {
   log_name="/tmp/test-${tools[i]}-${architecture[$m]}-${k}.log"
   # Clean is probably necessary for XST
   make clean > $log_name
   make ${tools[i]} >> $log_name
   if [ "${tools[i]}" = "xst" ]; then
      slices=`sed --posix -r '/[[:blank:]]*Number of Slices:[[:blank:]]*/!d; s///;q' $log_name | cut -f 1 -d " "`
      frequency=`sed --posix -r '/.*\(Maximum Frequency: */!d; s///;q' $log_name | cut -f 1 -d "M"`
   elif [ "${tools[i]}" = "precision" ]; then
      slices=`sed --posix -r '/[^C]*CLB Slices[[:blank:]]*/!d; s///;q' $log_name | cut -f 1 -d " "`
      frequency=`sed --posix -r -n '/Min Period \(Freq\)/!d;n;n;s/[^(]*\(//p;q' $log_name | cut -f 1 -d " "`
   fi
   cat << EOT
      <tr>
         <td>$fpga</td>
         <td>${architecture[$m]}</td>
         <td>${tools[i]}</td>
         <td>$generics_output</td>
         <td>$slices</td>
         <td>$frequency</td>
      </tr>
EOT
}

declare -a tools         # Tools for testing, eg. precision, xst
declare -a tools_scripts # Name of the tool script, eg. Precision.tcl
declare    toplevel=""   # Filename for testing
declare    fpga=""       # FPGA chip name
declare -a architecture  # Architectures for testing scripts
declare -a generics_count # This array contains numbers - how many
# components has first, second, ... generics tag
declare -a generics      # Generics itself, one-dimensional array
declare -i fpga_in_xml=0
declare -i frequency_in_xml=0

function parse ()
{
   for (( doall=0; doall < $xINDEX; doall++ )) ;
   do
      #      echo -e "${xmlSTAT[doall]}"":""${xmlDATA[doall]}" # Original echo

      # Nothing to do with closing tags...
      if [ ${xmlSTAT[doall]} = ">" ] ; then
         continue;
      fi
      case ${xmlDATA[doall]} in
         'synthesis')
         # Dummy tag...
         ;;
         'tool')
         ((doall++))
         tools[${#tools[@]}]=${xmlDATA[doall]}
         ;;
         'toplevel')
         ((doall++))
         toplevel=${xmlDATA[doall]}
         ;;
         'fpga')
         ((doall++))
         fpga=${xmlDATA[doall]}
         fpga_in_xml=1
         ;;
         'archgrp')
         ((doall++))
         architecture[${#architecture[@]}]=${xmlDATA[doall]}
         ;;
         'generics')
         ((doall++))
         generics_count[${#generics_count[@]}]=0
         while [ ${xmlSTAT[doall]} != ">" -a ${xmlDATA[doall]} != "generics" ] ;
         do
            # There should be the opening generic tag
            if [ ${xmlSTAT[doall]} != "<" -o ${xmlDATA[doall]} != "generic" ] ; then
               err "generic open tag expected in generics"
            fi
            # We have another one generic tag
            ((generics_count[${#generics_count[@]} - 1]++))
            # Fill the array of generic (name and value)
            ((doall++))
            generics[${#generics[@]}]=${xmlDATA[doall]};
            ((doall++))
            generics[${#generics[@]}]=${xmlDATA[doall]};
            # Move
            ((doall++))
            # There should be the closing generic tag
            if [ ${xmlSTAT[doall]} != ">" -o ${xmlDATA[doall]} != "generic" ] ; then
               err "generic close tag expected in generics"
            fi
            ((doall++))
         done
         ;;
         'frequency')
         frequency_in_xml=1
         ((doall++))
         frequency_pin=${xmlDATA[doall]}
         ((doall++))
         frequency_mhz=${xmlDATA[doall]}
         ((doall++))
         if [ ${xmlSTAT[doall]} != ">" -o ${xmlDATA[doall]} != "frequency" ] ; then
            err "The frequency close tag is expected after the frequency value."
         fi
         ;;
         *)
         err "Unexpected tag (value): ${xmlDATA[doall]}"
         ;;
      esac
   done
}

# Testing script begins here
# Control variables are made during parsing of synthesis.xml
# The testing script itself comes after that

# Make testing variables
parse

# Check input data
if [ ${#tools[@]} -lt 1 ] ; then
   err "At least one tool in tag <tool> must be specified"
fi

if [ "$toplevel" = "" ] ; then
   err "Toplevel file (tag <toplevel>) must be specified"
fi

# Backup the original file
# Check writeable
if [ ! -w ../$toplevel ] ; then
   err "Toplevel file ($toplevel) not exists/writeable"
fi

# Check, if there is a .orig file (we shouldn't overwrite this file)
if [ -e ../$toplevel.orig ] ; then
   err "Backup file $toplevel.orig already exists. Remove or backup it first"
fi

# Everything seems to be ok, so backup
cp ../$toplevel ../$toplevel.orig
if [ $? != 0 ] ; then
   err "Backup of the toplevel file failed."
fi

# We have at least one backup
backup=1

# Also backup original testing scripts
cp Precision.tcl Precision.tcl.orig
if [ $? != 0 ] ; then
   err "Backup of the Precision.tcl file failed."
fi

cp XST.tcl XST.tcl.orig
if [ $? != 0 ] ; then
   err "Backup of the XST.tcl file failed."
fi

# Table heading, output begin
cat << EOT
<h1>Frequency and resources usage</h1>
<p>
   <tab sloupce="cccccc">
   <tr>
      <th>FPGA</th>
      <th>Architecture</th>
      <th>Tool</th>
      <th>Generic settings</th>
      <th>Slices</th>
      <th>Max. Frequency</th>
   </tr>
EOT

# Make testing scripts and perform tests
for (( i=0; i < ${#tools[@]} ; i++ )) ;
do
   tool_file=""
   if [ ${tools[$i]} = "precision" ] ; then
      tools_scripts[$i]="Precision.tcl"
      if [ $frequency_in_xml -eq 1 ]; then
         frequency_value=$(( 1000 / $frequency_mhz ))
      fi
   elif [ ${tools[$i]} = "xst" ] ; then
      tools_scripts[$i]="XST.tcl"
      if [ $frequency_in_xml -eq 1 ]; then
         frequency_value=$frequency_mhz
      fi
   else
      err "Unrecognized tool: ${tools[$i]}"
   fi

   # Some variables
   declare -i generics_index=0
   declare -a sed_commands
   declare    generics_output=""

   # FPGA chip resolution
   fpga_in_template=`sed -n --posix -r '/^[[:blank:]]*set SYNTH_FLAGS\(FPGA\)[^"]*"/!d;s///;s/".*$//p;q' ${tools_scripts[$i]}`
   if [ $fpga_in_xml -eq 0 ] ; then
      fpga=$fpga_in_template
   fi

   # Is FPGA known?
   if [ "$fpga" = "" ] ; then
      err "FPGA chip resolution failed (chip not known)"
   fi

   # Architecture resolution
   if [ ${#architecture[@]} -eq 0 ]; then
      architecture[0]="FULL"
   fi

   # Change testing scripts
   for (( m=0; m < ${#architecture[@]} ; m++ )) ;
   do
      # Change clock if necessary
      if [ $frequency_in_xml -eq 1 ]; then
         if [ ${tools[$i]} = "xst" ]; then
            sed --posix -r '/SetTopAttribConstr/,/return/s/("NET \\")CLK(\\" PERIOD = )125(MHz HIGH 50%;".*)/\1'${frequency_pin}'\2'${frequency_value}'\3/' ${tools_scripts[$i]} > ${tools_scripts[$i]}.tmp
            return_value=$?
         else
            sed --posix -r '/SetTopAttribConstr/,/}/s/(create_clock -period )8 CLK(.*)/\1'${frequency_value}' '${frequency_pin}'/' ${tools_scripts[$i]} > ${tools_scripts[$i]}.tmp
            return_value=$?
         fi
         if [ $return_value -ne 0 ]; then
            err "Change of clock in testing script failed."
         fi
      else
         cp ${tools_scripts[$i]} ${tools_scripts[$i]}.tmp
         if [ $? -ne 0 ]; then
            err "Copy of testing script failed."
         fi
      fi
      # Change FPGA and architecture
      sed --posix -r \
      -e "s/$fpga_in_template/$fpga/" \
      -e 's/(set COMPONENTS \[list  \[list "MY_COMP"[^"]*")FULL("\]\])/\1'${architecture[$m]}'\2/' \
      ${tools_scripts[$i]}.tmp > ${tools_scripts[$i]}
      if [ $? -ne 0 ]; then
         err "Changing of the test script failed"
      fi
      rm ${tools_scripts[$i]}.tmp
      cp ${tools_scripts[$i]} /tmp/${fpga}-${architecture[$m]}-${tools_scripts[$i]}

      # If there aren't any generics
      if [ ${#generics_count[@]} -eq 0 ]; then
         generics_output=""
         k=0
         perform_test
      fi

      # If there are generics
      # Change the values in the original file and perform test (cycle, for each generics)
      generics_index=0
      for (( k=0; k < ${#generics_count[@]}; k++ )) ;
      do
         # Jump over the emtpy generics tag
         if [ ${generics_count[k]} = 0 ]; then
            continue
         fi
         unset sed_commands
         generics_output=""

         # Go through the generic in the one generics tag
         for (( j=0; j < ${generics_count[k]}; j++ )) ;
         do
            # Check the existence of tag and exclude comments
	    sed --posix -r "s/--.*//" ../$toplevel.orig |
            sed -n --posix -r "/generic/,/\)/p" | grep -E "${generics[$generics_index]}[[:blank:]]*:" >/dev/null
            if [ $? -ne 0 ]; then
               warn "Generic ${generics[$generics_index]} not found, cannot change."
            else
               generics_output=$generics_output"${generics[$generics_index]}=${generics[$generics_index+1]} "
               # Make sed commands based on generics
               # First sed command is for generic without default value
               sed_commands[${#sed_commands[@]}]="-e /generic/,/\)/s/(${generics[$generics_index]}[[:blank:]]*:[^;:]*)(;?[^:]*)$/\1 := ${generics[$generics_index+1]}\2/"
               sed_commands[${#sed_commands[@]}]="-e /generic/,/\)/s/(${generics[$generics_index]}.*:=[[:blank:]]*)[^;]*(;?.*)/\1${generics[$generics_index+1]}\2/"
            fi
            ((generics_index+=2))
         done
	 # Is here more then one sed command?
	 if [ ${#sed_commands[@]} -eq 0 ]; then
	    warn "There wasn't changed any generic"
	    cat ../$toplevel.orig > ../$toplevel
	 else
            # Here comes the sed editing the generic section of VHDL (and excluding comments)
	    sed --posix -r "s/--.*//" ../$toplevel.orig |
            sed --posix -r "${sed_commands[@]:0}" > ../$toplevel
            if [ $? -ne 0 ]; then
        	err "Editing of toplevel file failed."
            fi
	 fi
      perform_test
      done
   done
done

# Restore the original file
mv ../$toplevel.orig ../$toplevel
if [ $? != 0 ] ; then
   err "Return to the original $toplevel from original file failed!"
fi

# Remove created test scripts
for (( i=0; i < ${#tools_scripts[@]} ; i++ )) ;
do
   rm -f ${tools_scripts[$i]}
done

# Restore original test scripts
mv Precision.tcl.orig Precision.tcl
if [ $? != 0 ] ; then
   err "Return to the original Precision.tcl failed!"
fi

mv XST.tcl.orig XST.tcl
if [ $? != 0 ] ; then
   err "Return to the original XST.tcl failed!"
fi

# Table footer, output end
cat << EOT
<nazev>Chip utilization and maximal frequency.</nazev>
</tab>
</p>
EOT

# End of script
