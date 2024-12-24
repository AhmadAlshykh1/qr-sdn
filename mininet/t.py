from mininet.net import Mininet
from mininet.node import Controller, RemoteController, OVSController
from mininet.node import CPULimitedHost, Host, Node
from mininet.node import OVSKernelSwitch, UserSwitch
from mininet.cli import CLI
from mininet.log import setLogLevel, info
from mininet.link import TCLink, Intf
from threading import Thread
import os, stat
import json
import time
import csv
import http.client
import ssl
import sys
import math
from _thread import start_new_thread

sys.path.append("...")
sys.path.append("..")
sys.path.append("../controller")
sys.path.append(".")
print(os.getcwd())
print(sys.path.__str__())
from config import Config

#             s2
#  h11   10ms/     \10ms    h41
#     -- s1          s4 --
#  h12    14ms\     /14ms   h42
#             s3

###################################################################
############### Scenario - 6 Hosts    #############################
###################################################################

controller_ips = ['127.0.0.1', '127.0.0.1']  # IPs of the two controllers
controller_ports = [6633, 6653]  # Ports of the two controllers
controller_rest_ports = [8080, 8090]  # REST API ports of the two controllers

def reset_load_level(loadLevel, controller_rest_port):
    try:
        context = ssl._create_unverified_context()
        conn = http.client.HTTPConnection('0.0.0.0', controller_rest_port)
        headers = {'Content-Type': 'application/json'}
        load_level_data = json.dumps({"load_level": loadLevel})
        reset_flag_data = json.dumps({"reset_flag": True})
        conn.request('PUT', '/simpleswitch/params/load_level', body=load_level_data, headers=headers)
        conn.getresponse()
        conn.request('PUT', '/simpleswitch/params/reset_flag', body=reset_flag_data, headers=headers)
        conn.getresponse()
        conn.close()
    except Exception as e:
        print(f"Error communicating with controller on port {controller_rest_port}: {e}")

def reset_iteration(iteration, controller_rest_port):
    try:
        context = ssl._create_unverified_context()
        conn = http.client.HTTPConnection('0.0.0.0', controller_rest_port)
        headers = {'Content-Type': 'application/json'}
        iteration_data = json.dumps({"iteration": iteration})
        iteration_flag_data = json.dumps({"iteration_flag": True})
        conn.request('PUT', '/simpleswitch/params/iteration', body=iteration_data, headers=headers)
        conn.getresponse()
        conn.request('PUT', '/simpleswitch/params/iteration_flag', body=iteration_flag_data, headers=headers)
        conn.getresponse()
        conn.close()
    except Exception as e:
        print(f"Error communicating with controller on port {controller_rest_port}: {e}")

def stop_controller(controller_rest_port):
    try:
        context = ssl._create_unverified_context()
        conn = http.client.HTTPConnection('0.0.0.0', controller_rest_port)
        headers = {'Content-Type': 'application/json'}
        stop_flag_data = json.dumps({"stop_flag": True})
        conn.request('PUT', '/simpleswitch/params/stop_flag', body=stop_flag_data, headers=headers)
        conn.getresponse()
        conn.close()
    except Exception as e:
        print(f"Error communicating with controller on port {controller_rest_port}: {e}")

def startIperf(host1, host2, amount, port, timeTotal, loadLevel):
    bw = float(amount) * (float(loadLevel) / float(10))
    print("Host {} to Host {} Bw: {}".format(host1.name, host2.name, bw))
    command = "iperf -c {} -u -p {} -t {} -b {}M &".format(host2.IP(), port, timeTotal, bw)
    host1.cmd(command)

def write_in_File(fileName, logs, loadlevel, iteration_split_up_flag, iteration):
    dir = logs + '/'
    if iteration_split_up_flag:
        dir = dir + str(iteration) + '/'
    with open('{}{}.csv'.format(dir, fileName), 'a') as csvfile:
        fileWriter = csv.writer(csvfile, delimiter=',')
        fileWriter.writerow([loadlevel, time.time()])

def clearingSaveFile(fileName, logs):
    dir = logs + '/'
    with open('{}{}.csv'.format(dir, fileName), 'w') as file:
        file.write("# loadlevel, timestamp \n")

def clearing_save_file_iterations(fileName, logs, iterations):
    for iteration in range(iterations):
        dir = logs + '/' + str(iteration) + '/'
        if not os.path.exists(dir):
            os.makedirs(dir)
            os.chmod(dir, stat.S_IRWXO)
        with open('{}{}.csv'.format(dir, fileName), 'w') as file:
            file.write("# loadlevel, timestamp \n")

def min_to_sec(min):
    return min * 60

def four_switches_network():
    net = Mininet(topo=None,
                  build=False,
                  ipBase='10.0.0.0/8', link=TCLink)

    queue_lenght = Config.queue_lenght
    bw_max_dict = Config.bw_max_dict
    linkArray = []
    split_up_load_levels_flag = Config.split_up_load_levels_flag
    logs = Config.log_path
    loadLevels = Config.load_levels
    print("LoadLevel: {}".format(loadLevels))
    timeTotal = min_to_sec(Config.duration_iperf_per_load_level_minutes)
    fileName = 'timestamp_changing_load_levels_mininet'

    info('*** Adding controllers\n')
    controllers = []
    for i in range(2):
        c = net.addController(name=f'c{i}',
                               controller=RemoteController,
                               ip=controller_ips[i],
                               protocol='tcp',
                               port=controller_ports[i])
        controllers.append(c)


    info('*** Add switches\n')
    s1 = net.addSwitch('s1', cls=OVSKernelSwitch)
    s2 = net.addSwitch('s2', cls=OVSKernelSwitch)
    s3 = net.addSwitch('s3', cls=OVSKernelSwitch)
    s4 = net.addSwitch('s4', cls=OVSKernelSwitch)

    info( '*** Add hosts\n')
    h11 = net.addHost('h11', cls=Host, ip='10.0.0.11', defaultRoute=None)
    h12 = net.addHost('h12', cls=Host, ip='10.0.0.12', defaultRoute=None)
    h13 = net.addHost('h13', cls=Host, ip='10.0.0.13', defaultRoute=None)

    h41 = net.addHost('h41', cls=Host, ip='10.0.0.41', defaultRoute=None)
    h42 = net.addHost('h42', cls=Host, ip='10.0.0.42', defaultRoute=None)
    h43 = net.addHost('h43', cls=Host, ip='10.0.0.43', defaultRoute=None)

    info('*** Add links\n')
    linkArray.append(net.addLink(s1, s2, delay='10ms',use_tbf = True, bw=3, max_queue_size=queue_lenght, latency_ms = 10000000, burst = 1000000))
    net.addLink(h11, s1)
    net.addLink(h12, s1)
    net.addLink(h13, s1)

    linkArray.append(net.addLink(s4, s3, delay='14ms',use_tbf = True, bw=4, max_queue_size=queue_lenght, latency_ms = 10000000, burst = 1000000))
    net.addLink(h41, s4)
    net.addLink(h42, s4)
    net.addLink(h43, s4)

    net.addLink(s2, s4, delay='10ms',use_tbf = True, bw=3, max_queue_size=queue_lenght, latency_ms = 10000000, burst = 1000000)


    info('*** Starting network\n')
    net.build()
    info('*** Starting controllers\n')
    for controller in net.controllers:
        controller.start()

    info('*** Starting switches\n')
    net.get('s1').start([controllers[0]])
    net.get('s2').start([controllers[0]])
    net.get('s3').start([controllers[1]])
    net.get('s4').start([controllers[1]])


    iterations = Config.iterations
    if iterations > 1:
        iteration_split_up_flag = True
    else:
        iteration_split_up_flag = False

    if not split_up_load_levels_flag:
        if iteration_split_up_flag:
            clearing_save_file_iterations(fileName, logs, iterations)
        else:
            clearingSaveFile(fileName, logs)


    time.sleep(15)  # Allow time for controllers and switches to connect


    for iteration in range(iterations):
        i = 0

        if iteration_split_up_flag:
            clearing_save_file_iterations(fileName, logs, iterations) # Clear the files at the start of each iteration

        for loadLevel in loadLevels:
            if split_up_load_levels_flag:
                for rest_port in controller_rest_ports:
                    reset_load_level(loadLevel, rest_port)
            if not split_up_load_levels_flag:
                write_in_File(fileName, logs, loadLevel, iteration_split_up_flag, iteration)

            print("(Re)starting iperf -- loadLevel:  {}".format(loadLevel))

            start_new_thread(startIperf, (h11, h41, 2.75, 5001, timeTotal, loadLevel))
            start_new_thread(startIperf, (h12, h42, 1.75, 5001, timeTotal, loadLevel))
            start_new_thread(startIperf, (h13, h43, 1.75, 5001, timeTotal, loadLevel))
            i = i + 1
            time.sleep(timeTotal)

            if Config.wait_between_load_lavel_change:
                time.sleep(Config.waiting_time)

        if not split_up_load_levels_flag:
            write_in_File(fileName, logs, -1, iteration_split_up_flag, iteration)
        if iteration_split_up_flag and iteration < iterations - 1:
            for rest_port in controller_rest_ports: # For each controller
                reset_iteration(iteration + 1, rest_port)
            time.sleep(1)


    for rest_port in controller_rest_ports:
        stop_controller(rest_port)

    CLI(net)
    net.stop()

if __name__ == '__main__':
    setLogLevel('info')
    four_switches_network()
