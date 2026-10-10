# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# Questa/ModelSim helpers for adding MVB and MFB buses to the Wave window.
#
# Usage, e.g. from a .fdo file once the design is loaded:
#
#   source $OFM_PATH/build/scripts/questa/wave_bus.tcl
#
#   # Every bus directly under an instance
#   set MVB_FMT(WQ_SEL_RSP) {WQID 4 ADDR 64 LEN 7}
#   mvb_add_wave_fmt_all /dut/wqe_cache_i
#   mfb_add_wave_all     /dut/wqe_cache_i
#
#   # A single bus
#   mvb_add_wave_fmt /dut/wqe_cache_i/WQ_SEL_RSP_MVB {WQID 4 ADDR 64 LEN 7}
#   mfb_add_wave     /dut/wqe_cache_i/RX_MFB
#
# A bus is identified by its <prefix>_SRC_RDY signal and added as a wave group
# named after the bus (suffix _MVB/_MFB dropped), nested in a group named after
# the enclosing unit (see bus_unit_group). Only <prefix>_DATA is mandatory.
#
# MVB
#   Signals DATA, VLD, SRC_RDY, DST_RDY. Each item gets a subgroup with a
#   "transfer" virtual function (SRC_RDY and DST_RDY and VLD) and its part of
#   DATA split into named fields. When DATA is an slv_array_t, each port gets
#   a subgroup, nesting the subgroups of its items.
#
#   A field layout is a flat {name width ...} list, lowest bits first. It may
#   describe only the low part of the item; the remaining bits are left out.
#   Describing more bits than the item holds is reported and the split is
#   skipped. A width of 0 denotes a field disabled by configuration and is
#   ignored. Layouts for *_all are looked up in the MVB_FMT array by bus name;
#   [mvb_variants ...] offers alternatives chosen by the actual item width.
#
# MFB
#   Signals DATA, META, SOF, EOF, SOF_POS, EOF_POS, SRC_RDY, DST_RDY and a
#   "transfer" virtual function (SRC_RDY and DST_RDY). The signals are shown
#   as they are; regions and frames are not decoded.

# ===========================================================================
#  Field layout
# ===========================================================================

# {name width ...} -> {{name low high} ...}, chained from bit 0 upwards.
proc mvb_resolve_fmt {fmt} {
    if {[llength $fmt] % 2 != 0} {
        error "MVB format must be a {name width ...} list, got [llength $fmt] element(s)"
    }
    set out {}
    set l 0
    foreach {name w} $fmt {
        if {![string is integer -strict $w] || $w < 0} {
            error "MVB format: width of field '$name' must be a non-negative integer, got '$w'"
        }
        if {$w == 0} {
            continue
        }
        set h [expr {$l + $w - 1}]
        lappend out [list $name $l $h]
        set l [expr {$h + 1}]
    }
    return $out
}

proc mvb_fields_span {resolved} {
    set span 0
    foreach f $resolved {
        if {[lindex $f 2] + 1 > $span} {
            set span [expr {[lindex $f 2] + 1}]
        }
    }
    return $span
}

# Wraps several alternative layouts for one bus. mvb_add_wave selects the
# alternative whose span matches the actual DATA item width, which resolves
# buses whose format depends on a generic or on the hierarchy level.
proc mvb_variants {args} {
    return [concat VARIANTS $args]
}

# ===========================================================================
#  Signal introspection
# ===========================================================================

# For an array of vectors (slv_array_t) this is the outer dimension, not a bit
# width; see mvb_sig_is_array.
proc mvb_sig_width {path} {
    if {[regexp {length (\d+)} [describe $path] - w]} {
        return $w
    }
    return 1
}

proc mvb_sig_is_array {path} {
    return [expr {[regexp {length \d+} [describe "${path}(0)"]] ? 1 : 0}]
}

# ===========================================================================
#  Bus discovery and group naming
# ===========================================================================

# Bus prefixes (e.g. WQ_SEL_RSP_MVB) of the given kind, among the ports and
# internal signals directly under $path.
proc bus_find {path {kind mvb}} {
    set re [format {.*/(\w*%s\w*)_src_rdy\Z} $kind]
    set out {}
    foreach opt {-ports -internal} {
        foreach s [find signals $opt "[string trimright $path /]/*"] {
            if {[regexp -nocase $re $s - name]} {
                if {[lsearch -exact $out $name] < 0} {
                    lappend out $name
                }
            }
        }
    }
    return $out
}

proc bus_name {bus} {
    regsub -nocase {_m[vf]b$} $bus {} bus
    return $bus
}

# Removed from the instance label by bus_unit_group; a design may extend this
# list with its own naming conventions.
if {![info exists ::BUS_UNIT_STRIP]} {
    set ::BUS_UNIT_STRIP {{_i$}}
}

# Questa adds signals to an existing group whenever the name matches, so buses
# of the same name in different units need distinct enclosing groups. The
# trailing digit is the innermost generate index, which keeps replicated units
# apart:  /tb/dut_g(0)/dut_i/unit_i -> unit0
proc bus_unit_group {path} {
    global BUS_UNIT_STRIP
    set segs [split [string trimright $path /] /]
    set name [lindex $segs end]
    foreach re $BUS_UNIT_STRIP {
        regsub $re $name {} name
    }
    set idx {}
    foreach seg $segs {
        if {[regexp {\((\d+)\)$} $seg - n]} {
            set idx $n
        }
    }
    return "$name$idx"
}

# Returns {gbase group}. Groups nest by repeating -group, outermost first;
# a single -group holding a name with a space would create one sibling group
# instead.
proc bus_groups {prefix outer group} {
    if {$group eq {}} {
        set group [bus_name [lindex [split $prefix /] end]]
    }
    if {$outer eq "auto"} {
        set outer [bus_unit_group [join [lrange [split $prefix /] 0 end-1] /]]
    }
    set gbase {}
    foreach og $outer {
        lappend gbase -group $og
    }
    lappend gbase -group $group
    return [list $gbase $group]
}

# Path of <prefix>_<suffix>, empty when the design has no such signal.
proc bus_signal {prefix suffix} {
    set sig "${prefix}_${suffix}"
    if {[llength [find signals $sig]] == 0} {
        return {}
    }
    return $sig
}

# Adds a "transfer" virtual function that is high while all $terms are.
# $idx holds the port and/or item index, if the bus has more than one of them.
proc bus_add_transfer {gbase prefix terms {idx {}}} {
    if {[llength $terms] == 0} {
        return
    }
    set bus [regsub -all {[^A-Za-z0-9_]} [lindex [split $prefix /] end] {_}]
    set name [join [concat $bus transfer $idx] __]
    set vf [virtual function "{[join $terms { and }]}" $name]
    add wave {*}$gbase -color yellow -label transfer $vf
}

# ===========================================================================
#  Engine
# ===========================================================================

# Adds one MVB bus to the Wave window.
#   prefix    path up to and including the bus name, e.g. /tb/dut_i/RX_MVB
#   fields    layout in the form understood by $resolver, or an
#             [mvb_variants ...] wrapper; an empty list adds the raw signals only
#   resolver  command prefix mapping $fields to a {{label low high} ...} list
#   outer     enclosing group name(s), outermost first. "auto" derives one from
#             the instance path, {} places the bus group at the top level.
#   group     wave group of the bus; defaults to the bus name from $prefix
proc mvb_add_wave {prefix fields resolver {outer auto} {group {}}} {
    set data [bus_signal $prefix DATA]
    if {$data eq {}} {
        echo "mvb_add_wave: no such MVB bus: $prefix"
        return
    }

    # A bus that is never stalled may have no _DST_RDY at all.
    set vld     [bus_signal $prefix VLD]
    set src_rdy [bus_signal $prefix SRC_RDY]
    set dst_rdy [bus_signal $prefix DST_RDY]

    lassign [bus_groups $prefix $outer $group] gbase group

    # A bus carries multiple transactions in one of these shapes:
    #   multi-item  DATA is one flat ITEMS*item_w vector, VLD has one bit per
    #               item, SRC_RDY/DST_RDY are shared
    #   multi-port  DATA is slv_array_t(PORTS)(ITEMS*item_w), i.e. PORTS
    #               independent buses: SRC_RDY/DST_RDY are PORTS-bit vectors
    #               and VLD is either a PORTS-bit vector (one item per port)
    #               or slv_array_t(PORTS)(ITEMS)
    set ports [mvb_sig_is_array $data]
    set vld_arr [expr {$ports && $vld ne {} && [mvb_sig_is_array $vld]}]
    if {$ports} {
        set nports [mvb_sig_width $data]
        set data_w [mvb_sig_width "${data}(0)"]
        set items  [expr {$vld_arr ? [mvb_sig_width "${vld}(0)"] : 1}]
    } else {
        set nports 1
        set data_w [mvb_sig_width $data]
        set items  [expr {$vld eq {} ? 1 : [mvb_sig_width $vld]}]
    }
    set item_w [expr {$data_w / $items}]

    # The raw signals go in once, above the per-item subgroups.
    add wave {*}$gbase -label DATA $data
    if {$vld ne {}} {
        add wave {*}$gbase -label [lindex [split $vld _] end] $vld
    }
    foreach sig [list $src_rdy $dst_rdy] {
        if {$sig ne {}} {
            add wave {*}$gbase -label [lindex [split $sig _] end-1]_[lindex [split $sig _] end] $sig
        }
    }

    # An unresolvable layout costs only the field split: the design may predate
    # a field the table names, and the raw signals and transfer are still worth
    # having. The first variant is kept on failure so that the width check
    # below reports a meaningful span. Each variant is tried on its own, so that
    # one unresolvable variant does not hide a later one that matches.
    if {[lindex $fields 0] eq "VARIANTS"} {
        set alts [lrange $fields 1 end]
        set fields [lindex $alts 0]
        foreach alt $alts {
            if {![catch {mvb_fields_span [{*}$resolver $alt]} span] && $span == $item_w} {
                set fields $alt
                break
            }
        }
    }
    if {[catch {set resolved [{*}$resolver $fields]} err]} {
        echo "mvb_add_wave: $prefix: layout not resolvable, field split skipped ($err)"
        set resolved {}
    }
    set span [mvb_fields_span $resolved]
    if {$data_w % $items != 0} {
        echo "mvb_add_wave: $prefix: DATA width $data_w is not a multiple of\
              $items item(s); field split skipped."
        set resolved {}
    } elseif {$span > $item_w} {
        echo "mvb_add_wave: $prefix: layout describes $span bit(s) but the DATA\
              item is only $item_w bit(s) wide; field split skipped."
        set resolved {}
    } elseif {$span > 0 && $span < $item_w} {
        echo "mvb_add_wave: $prefix: layout covers $span of $item_w bit(s)"
    }

    for {set p 0} {$p < $nports} {incr p} {
        for {set i 0} {$i < $items} {incr i} {
            set g $gbase
            set idx {}
            if {$ports} {
                lappend g -expand -group $p
                lappend idx $p
            }
            if {$items > 1} {
                lappend g -expand -group $i
                lappend idx $i
            }

            # A port is addressed by indexing every signal, an item by an
            # offset into the DATA vector and by a bit of VLD.
            set psel [expr {$ports ? "($p)" : ""}]
            set terms {}
            foreach sig [list $src_rdy $dst_rdy] {
                if {$sig ne {}} {
                    lappend terms "${sig}${psel}"
                }
            }
            if {$vld ne {}} {
                lappend terms [expr {$vld_arr || !$ports ? "${vld}${psel}($i)" : "${vld}${psel}"}]
            }
            set dsel "${data}${psel}"
            set off  [expr {$i * $item_w}]

            bus_add_transfer $g $prefix $terms $idx

            foreach f $resolved {
                set l [expr {[lindex $f 1] + $off}]
                set h [expr {[lindex $f 2] + $off}]
                add wave {*}$g -label [lindex $f 0] "${dsel}($h downto $l)"
            }
        }
    }
}

# Layouts come from the array named by $table, indexed by bus name without the
# _MVB suffix. A failing bus is reported and skipped, so that it cannot abort
# the whole walk.
proc mvb_add_wave_all {path table resolver {outer auto}} {
    upvar #0 $table tbl
    foreach bus [bus_find $path mvb] {
        set name [bus_name $bus]
        set fields {}
        if {[info exists tbl($name)]} {
            set fields $tbl($name)
        }
        set prefix "[string trimright $path /]/$bus"
        if {[catch {mvb_add_wave $prefix $fields $resolver $outer $name} err]} {
            echo "mvb_add_wave_all: skipped $prefix: $err"
        }
    }
}

# ===========================================================================
#  MFB
# ===========================================================================

# Adds one MFB bus; its META and DST_RDY signals are optional.
proc mfb_add_wave {prefix {outer auto} {group {}}} {
    if {[bus_signal $prefix DATA] eq {}} {
        echo "mfb_add_wave: no such MFB bus: $prefix"
        return
    }
    lassign [bus_groups $prefix $outer $group] gbase group

    foreach suffix {DATA META SOF EOF SOF_POS EOF_POS SRC_RDY DST_RDY} {
        set sig [bus_signal $prefix $suffix]
        if {$sig ne {}} {
            add wave {*}$gbase -label $suffix $sig
        }
    }

    set terms {}
    foreach suffix {SRC_RDY DST_RDY} {
        set sig [bus_signal $prefix $suffix]
        if {$sig ne {}} {
            lappend terms $sig
        }
    }
    bus_add_transfer $gbase $prefix $terms
}

# Adds every MFB bus found directly under $path.
proc mfb_add_wave_all {path {outer auto}} {
    foreach bus [bus_find $path mfb] {
        set prefix "[string trimright $path /]/$bus"
        if {[catch {mfb_add_wave $prefix $outer [bus_name $bus]} err]} {
            echo "mfb_add_wave_all: skipped $prefix: $err"
        }
    }
}

# ===========================================================================
#  MVB
# ===========================================================================

# Layouts used by mvb_add_wave_fmt_all, indexed by bus name without _MVB:
#   set MVB_FMT(WQ_SEL_RSP) {WQID 4 ADDR 64 LEN 7}
if {![info exists ::MVB_FMT]} {
    array set ::MVB_FMT {}
}

# Adds one MVB bus, its layout given as a {name width ...} list.
proc mvb_add_wave_fmt {prefix fmt {outer auto} {group {}}} {
    mvb_add_wave $prefix $fmt mvb_resolve_fmt $outer $group
}

# Adds every MVB bus found directly under $path, using the layouts in MVB_FMT.
proc mvb_add_wave_fmt_all {path {outer auto}} {
    mvb_add_wave_all $path MVB_FMT mvb_resolve_fmt $outer
}
