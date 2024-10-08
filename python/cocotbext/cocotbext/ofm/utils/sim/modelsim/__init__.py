import logging
import builtins
import sys

from ctypes import cdll, c_void_p, c_char_p, c_int

#__lib = cdll.LoadLibrary('/opt/modeltech/modeltech/linux_x86_64/libmtipli.so')
__lib = cdll.LoadLibrary('libmtipli.so')

__lib.mti_Cmd.argtypes = [c_char_p]
__lib.mti_Cmd.restype = c_int

__lib.mti_Break.argtypes = []

__lib.mti_Interp.argtypes = []
__lib.mti_Interp.restype = c_void_p

__lib.Tcl_GetStringResult.argtypes = [c_void_p]
__lib.Tcl_GetStringResult.restype = c_char_p

__lib.Tcl_ResetResult.argtypes = [c_void_p]

try:
    __interp = __lib.mti_Interp()
    assert __interp
except Exception:
    logger = logging.getLogger("modelsim")
    logger.warn("can't load modelsim interpreter handle.")


def cmd(command):
    __lib.mti_Cmd(command.encode())
    res = __lib.Tcl_GetStringResult(__interp)
    ret = res.decode()
    __lib.Tcl_ResetResult(__interp)
    return ret


def mti_break():
    __lib.mti_Break()


def print(*args, **kwargs):
    builtins.print(*args, **kwargs)
    sys.stdout.flush()


def cocotb2path(obj):
    return "/" + obj._path.replace(".", "/").replace("[", "(").replace("]", ")")


def add_wave(*args, **kwargs):
    # TODO: translate kwargs to some of these:
    #[-allowconstants] [-clampanalog {0|1}] [-color <standard_color_name>] [-depth <level>] [-divider <divider_name>...] [-expand <signal_name>] [-filter <f> | -nofilter <f>] [-format <type> | -<format>] [-group <group_name> [<sig_name1>...]] [-height <pixels>] [[-in] [-out] [-inout] | [-ports]] [-internal] [-label <name>] [-max <real_num>] [-min <real_num>] [-mvcall] [-mvcovm] [-mvcreccomplete] [-noupdate] [-numdynitem <int>] [-optcells] [-position <location>] [-queueends] [-radix <type> | -<radix_type>] [-radixenumnumeric | -radixenumsymbolic] [-recursive] [-startdynitem <int>] [-time] [-window <wname>] [<object_name>...] [{<object_name> {sig1 sig2 ...}}] # noqa

    name = ""
    for obj in args:
        if isinstance(obj, str):
            name += " " + obj
        else:
            name += " {" + cocotb2path(obj) + "}"
    params = ""
    if 'group' in kwargs:
        params += f' -group "{kwargs["group"]}" '
        # Nested grouping also possible, just use more -group switches.
        # This should be done by new kwarg, for example. cmd_prefix='-group base_group_name'
    if 'expand' in kwargs:
        params += ' -expand'# "{kwargs["expand"]}"'
    if 'label' in kwargs:
        params += f' -label {{{kwargs["label"]}}}'

    if 'bus' in kwargs:
        params += f" -label {name} "
        name = "{" + name + " {" + " ".join([cocotb2path(o) + f"[{r.stop - 1}:{r.start}]" for o, r in kwargs['bus']]) + "}}"

    cmd("add wave" + params + name)
