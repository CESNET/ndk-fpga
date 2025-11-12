import logging
import builtins
import sys

from ctypes import cdll, c_void_p, c_char_p, c_int

import cocotb.utils


st = cocotb.utils.get_sim_time

#__lib = cdll.LoadLibrary('/opt/modeltech/modeltech/linux_x86_64/libmtipli.so')
try:
    __lib = cdll.LoadLibrary('libmtipli.so')

    __lib.mti_Cmd.argtypes = [c_char_p]
    __lib.mti_Cmd.restype = c_int

    __lib.mti_Break.argtypes = []

    __lib.mti_Interp.argtypes = []
    __lib.mti_Interp.restype = c_void_p

    __lib.Tcl_GetStringResult.argtypes = [c_void_p]
    __lib.Tcl_GetStringResult.restype = c_char_p

    __lib.Tcl_ResetResult.argtypes = [c_void_p]

    __interp = __lib.mti_Interp()
    assert __interp
except Exception:
    __lib = None
    logger = logging.getLogger(__name__)
    logger.warn("can't load modelsim interpreter handle.")


def cmd(command):
    if __lib is None:
        return
    __lib.mti_Cmd(command.encode())
    res = __lib.Tcl_GetStringResult(__interp)
    ret = res.decode()
    __lib.Tcl_ResetResult(__interp)
    return ret


def mti_break():
    if __lib is None:
        return
    __lib.mti_Break()


def print(*args, **kwargs):
    builtins.print(*args, **kwargs)
    sys.stdout.flush()


def cocotb2path(obj, slice=()):
    if __lib is None:
        return ""

    bp = "/" + obj._path.replace(".", "/").replace("[", "(").replace("]", ")")
    sl = ""
    if len(slice) == 1:
        sl = f"[{slice[0]}]"
    elif len(slice) == 2:
        sl = f"[{slice[1]-1}:{slice[0]}]"
    return bp + sl


def add_wave(*args, **kwargs):
    # TODO: translate kwargs to some of these:
    #[-allowconstants] [-clampanalog {0|1}] [-color <standard_color_name>] [-depth <level>] [-divider <divider_name>...] [-expand <signal_name>] [-filter <f> | -nofilter <f>] [-format <type> | -<format>] [-group <group_name> [<sig_name1>...]] [-height <pixels>] [[-in] [-out] [-inout] | [-ports]] [-internal] [-label <name>] [-max <real_num>] [-min <real_num>] [-mvcall] [-mvcovm] [-mvcreccomplete] [-noupdate] [-numdynitem <int>] [-optcells] [-position <location>] [-queueends] [-radix <type> | -<radix_type>] [-radixenumnumeric | -radixenumsymbolic] [-recursive] [-startdynitem <int>] [-time] [-window <wname>] [<object_name>...] [{<object_name> {sig1 sig2 ...}}] # noqa

    # The '-expand' precedes a '-group' (or more specific groups) and can be postponed e.g. with '-recursive /NONEXISTING'

    name = ""
    for obj in args:
        if isinstance(obj, str):
            name += f" {{{obj}}}"
        else:
            name += " {" + cocotb2path(obj) + "}"
    params = ""

    groups = kwargs.get("groups", [])
    if 'group' in kwargs:
        groups.append(kwargs['group'])

    expand = kwargs.get("expand", [])
    for i, g in enumerate(groups):
        if i in expand:
            params += " -expand "
        params += f' -group "{g}" '

    for p in ["label", "color"]:
        if p in kwargs:
            params += f' -{p} {{{kwargs[p]}}} '

    if 'bus' in kwargs:
        params += f" -label {name} "
        name = "{" + name + " {" + " ".join([cocotb2path(o) + f"[{r.stop - 1}:{r.start}]" for o, r in kwargs['bus']]) + "}}"

    cmd("add wave" + params + name)


def add_cursor(name=None, time=None, lock=True):
    if time is None:
        time = st()

    a = cmd("wave cursor active")
    c = f"wave cursor add -lock {1 if lock else 0} -time {{{time} ps}}" + ("" if name is None else f" -name {{{name}}}")
    n = cmd(c)
    cmd(f"wave cursor active {a}")
    return n
