# Profile_swap.py: Script for profile swap in Multirate IP cores
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jakub Záhora <xzahor06@vutbr.cz>

# Datasheet for F-Tile_Multirate
# https://cdrdv2-public.intel.com/773503/ug-714307-773503.pdf

# Datasheet for Dynamic reconfiguration controler
# https://cdrdv2-public.intel.com/767542/ug20341-711009-767542.pdf

# import lib
import argparse
import nfb
import ftile

# mi_bus location of  page for mi_select
p_mi_bus = 11

# Create the parser
args = argparse.ArgumentParser(description = "Multirate config setup Tool")
# Add an argument
args.add_argument("-s_ch","--start_channel", type=int, required=False, help="start channel for profile swap default value is 0", default=0)
args.add_argument("-ch","--channels", type=int, required=True, help="num. of channels to be changed (depends on type of used IP_core)")
args.add_argument("-s_p","--start_profile", type=int, required=False,help="which profile is used right now", default=1)
args.add_argument("-e_p","--end_profile", type=int, required=True,help="which profile you want to use as next")
args.add_argument("-sp","--speed", type=str, required=True,help="speed of used IP_Core you can use \n'2x100G-4'\n'8x25G-1'", default="8x25G-1")
args.add_argument("-d","--device", type=int, required=True,help="Choose device, in which you have implemented design", default=0)
arguments = args.parse_args()

# =========================
# Definition of parameters 
# =========================
# for start channel you need to count from 0 it is beacose first IP core is declarated on channel 0
# for channels you need to remember that total number of channels + start channel must be smaller or equal as number of channels that means for example
# for 100GE is correct combination start channel = 0 and channels = 2 and 
# for 100GE is wrong combination start channel = 1 and channels = 2 beacose there are only 2 IP cores and this combination means there must be 3 or more IP cores
# start profile represent current profile which is used default for our IP cores is profile 1 also dont forget if you change profile start profile must be last used profile 
# end profile represent profile, which you want to set as new profile  for use look for range of profile numbers for each IP core or use value of profile_difs
# speed represent speed of Reconfiguration IP (default IP used in build) so if you use 10G variant form 25G IP core you need still for profile swap use 25G IP core declaration

PROFILES_GROUPS = []
device_v = []
component = []
Profiles = []

# division into classes (types) of used multirate
# 100G-2 Profile
if arguments.speed == "2x100G-4":
    # protection in case of setting inappropriate parameters
    if arguments.start_channel > 1 or arguments.start_channel < 0:
        print("There are not that many channels, only 2 \n0\n1")
        exit()
    if arguments.channels + arguments.start_channel >= 3 or arguments.channels + arguments.start_channel <= 0 or arguments.channels <= 0:
        print("You are out of range of channels, it can be only \n1\n2")
        print("For example start_channel = 0 a channels = 2")
        exit()
    if arguments.start_profile <= 0 or arguments.start_profile >= 3:
        print("There are not that many start_profiles, only 2 \n1\n2")
        exit()   
    if arguments.end_profile <= 0 or arguments.end_profile >= 3:
        print("There are not that many end_profiles, only 2 \n1\n2")
        exit()      
    # inicialization
    profiles_difs = 2
    eth_channels = 2
    FEC_TYPE = [2,0]
    FEC = FEC_TYPE[arguments.end_profile - 1]
    profile_sel = 0
    Eth_25G_10G = 0
# 25G-1 Profile
elif arguments.speed == "8x25G-1":
    # protection in case of setting inappropriate parameters
    if arguments.start_channel > 7 or arguments.start_channel < 0:
        print("There are not that many channels, only 8 \n0\n1\n2\n3\n4\n5\n6\n7")
        exit()
    if arguments.channels + arguments.start_channel > 8 or arguments.channels + arguments.start_channel < 1 or arguments.channels <= 0:
        print("You are out of range of channels, it can be only \n1\n2\n3\n4\n5\n6\n7\n8")
        print("For example start_channel = 0 a channels = 8")
        exit()
    if arguments.start_profile <= 0 or arguments.start_profile >= 5:
        print("There are not that many start_profiles, only 4 \n1\n2\n3\n4")
        exit()
    if arguments.end_profile <= 0 or arguments.end_profile >= 5:
        print("There are not that many end_profiles, only 4 \n1\n2\n3\n4")
        exit()
    # inicialization
    profiles_difs = 4
    eth_channels = 8
    FEC_TYPE = [0,2,3,0]
    FEC = FEC_TYPE[arguments.end_profile - 1]
    ETH_SPEED = [0,0,0,1]
    Eth_25G_10G = ETH_SPEED[arguments.end_profile - 1]
    profile_sel = 0

else:
    # protection in case of setting inappropriate type of eth
    print("Choose correct speed :\n'2x100G-4'\n'8x25G-1'")
    exit()

# generator for full list of profiles, devices, components
for j in range (profiles_difs):
    PROFILES_GROUPS.append([])
    for i in range (eth_channels):
        device_v.append(i)
        component.append(i)
        PROFILES_GROUPS[j].append(j + i*profiles_difs+1 )

# initial initialization + line opening
dev = nfb.open(path=str(arguments.device))
nodes = dev.fdt_get_compatible("netcope,pcsregs")

node = []
comp = []

# initialization to open eth channels
for i in range (eth_channels):
    node.append(nodes[component[i]])
    comp.append(dev.comp_open(node[i]))

print()
print()
# ================================
# Description of main loop process
# ================================
# First step is to open path to device which is written before main loop
# Next step is to chech DR_Controler ready status flag after this flag is set to 0 you can start with reconfiguration while reg(0) = 0x3 you need to wait
# After flag is set to 0 next step is to put eth lines into reset for device (IP) which profile you want to change
# Next step is to write into DR_Contorel always use device = 0 it is beacose in build DR_Controler is instanced into network_mod_core(0)
# First disable profile which was used for example if you want to disable default profile(1) write value 0x0001 into register 0x4
# Second is to eneable next profile to be used for example profile(4) write value 0x8004, (where 8 is used as eneable bit(15) and 4 represents hexa value of choosen profile) into register 0x08.
# After you have changed values in DR_Controler register next step is to trigger reconfiguration by setting value of Ready for new trigger from 0 to 1 reg(0) = 0x1.
# After that do not try to change any parameter while this reg(0) = 3 wait while New Trigger Aplied value is  set back to reg(0) = 0x2 (check by pooling for value of reg).
# Next step is to rewrite parameters of F-Tile multirate chech dofumentation of F-Tile Multirate for more informations
# After all parameters are rewrite next step is to clear reset from eth. lines
# This process is repeated value of parameter cahnnels times

# MAIN LOOP
for i in range (arguments.channels):
    # print old config before swap
    print ("\nold config is:")
    eth = ftile.ftile_eth(comp[arguments.start_channel + i])

    # wait for moment when dr_controler is ready for switching profile
    val = ftile.drp_read_drc(comp[0], 0x0, p_mi_bus)  
    while val != 2:
        print("It is not yet possible to switch a profile, wait\n")
        val = ftile.drp_read_drc(comp[0], 0x0, p_mi_bus)  

    # dr_controler is ready, reset eth line for setup
    eth.set_reset()

    # setup dr_controler parameters
    print("\n\nSetting the profile in the process:", component[arguments.start_channel + i])
    ftile.drp_write_drc(comp[0], 0x4, PROFILES_GROUPS[arguments.start_profile-1][arguments.start_channel + i], p_mi_bus)
    ftile.drp_write_drc(comp[0], 0x8, 32768+PROFILES_GROUPS[arguments.end_profile-1][arguments.start_channel + i], p_mi_bus)

    # profile swap trigger
    ftile.drp_write_drc(comp[0], 0x0, 0x1, p_mi_bus)

    # wait for moment when dr_controler is ready after switching profile
    val = ftile.drp_read_drc(comp[0], 0x0, p_mi_bus)
    while val != 2:
        print("It is not yet possible to set up a profile, wait")
        val = ftile.drp_read_drc(comp[0], 0x0, p_mi_bus)

    # setup multirate parameters
    print("target ftile is :", device_v[i])
    ftile.drp_write(comp[arguments.start_channel + i], 0x200, profile_sel, device_v[0])
    ftile.drp_write(comp[arguments.start_channel + i], 0x204, FEC, device_v[0])
    ftile.drp_write(comp[arguments.start_channel + i], 0x208, Eth_25G_10G, device_v[0])

    # clear reset of eth lines after profile swap is completed
    eth.clr_reset()

    # print new set config after swap
    print ("\nnew config is:")
    eth = ftile.ftile_eth(comp[arguments.start_channel + i])
