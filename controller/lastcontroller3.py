
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.packet import packet, arp, ethernet, ipv4, ipv6, ether_types, icmp
from ryu.lib import hub
from ryu.app import simple_switch_13
from ryu.app.wsgi import ControllerBase, WSGIApplication, route, Response
from enum import Enum
from multiprocessing import Process, Pipe
from collections import defaultdict
import random
import time
import copy
import json
import sys
import networkx as nx
#import requests
import http.client
sys.path.append("..")
import learning_module
import functions
from config import Config, BiasRL, ActionMode, QMode
from routing_spf import RoutingShortestPath
import sys
import eventlet
import ssl
from flask import Flask, jsonify, request, Response
from ryu.app.wsgi import ControllerBase, route
import logging 
from eventlet.green import socket
eventlet.monkey_patch()
sys.setrecursionlimit(2000)
class RoutingType(Enum):
    DFS = 1
    DIJKSTRA = 2
    RL_GRAPH = 3
    RL_DFS = 4
ROUTING_TYPE = RoutingType.DFS
interval_communication_processes = Config.interval_communication_processes
interval_update_latency = Config.interval_update_latency
interval_controller_switch_latency = Config.interval_controller_switch_latency
REFERENCE_BW = 10000000
MAX_PATHS = 2
ADDITIONAL_WAITING_TIME = 10
LOOPBACK_IP = "127.0.0.1"
DEFAULT_BW = 10000000
simple_switch_instance_name = 'simple_switch_api_app'
url = '/simpleswitch/params/{obj}'
class ControllerMain(simple_switch_13.SimpleSwitch13):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _CONTEXTS = {'wsgi': WSGIApplication}
    def __init__(self, *args, **kwargs):
        super(ControllerMain, self).__init__(*args, **kwargs)
        wsgi = kwargs['wsgi']
        wsgi.register(SimpleSwitchController, {simple_switch_instance_name: self})
        self.waitTillStart = 0
        self.last_print_time = time.time()
        self.latency_measurement_flag = False
        self.mac_to_port = {}
        self.dpidToDatapath = {}
        self.arp_table = {}
        self.paths_per_flows = {}
        self.chosen_path_per_flow = {}
        self.PROBE_PACKET_ETHERTYPE = 0x07c3
        self.datapath_list = {}
        self.arp_table = {}
        self.switches = []
        self.hosts = {}
        self.adjacency = defaultdict(dict)
        self.bandwidths = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))
        self.routing_shortest_path = RoutingShortestPath()
        self.echo_sent_to_dpid = {}
        self.rtt_to_dpid = {}
        self.rtt_stats_sent = {}
        self.saved_rtt_to_dpid = {}
        self.saved_echo_rtt_to_dpid = {}
        self.saved_echo_timeToSw = {}
        self.saved_echo_timeToC = {}
        self.saved_rtt_to_dpid_portStats = {}
        self.rtt_portStats_to_dpid = {}
        self.temp_bw_map_ports = {}
        self.temp_bw_map_flows = {}
        self.data_map = {}
        self.last_arrived_package = {}
        self.latency_dict = {}
        self.bandwith_port_dict = {}
        self.bandwith_flow_dict = {}
        self.best_route_rl = []
        self.already_routed = []
        self.already_routed_ip = []
        self.reset_flag = False
        self.load_level = Config.load_levels[0]
        self.iteration_flag = False
        self.iteration = 0
        self.stop_flag = False
        self.bias = Config.bias
        self.action_mode = Config.action_mode
        self.last_state_change = time.time()
        self.last_action = time.time()
        self.latency_dict_SPF = {}
        self.parent_conn, self.child_conn = Pipe()
        self.domain_id = Config.domain_id
        self.domain_switches = Config.domain_switches[str(self.domain_id)]
        self.neighbor_controllers = Config.neighbor_controllers.get(str(self.domain_id), {})
        self.topology_graph = nx.Graph()
        p = Process(target=learning_module.learning_module, args=[self.child_conn])
        p.start()
        hub.spawn(self.checking_updates)
    def get_routing_info(self):
        try:
            routing_info = {}
            for flow_id, path in self.chosen_path_per_flow.items():
                src_ip, dst_ip = functions.build_ip_adresses(flow_id)  
                if src_ip not in routing_info:
                    routing_info[src_ip] = {}
                routing_info[src_ip][dst_ip] = path
            self.logger.info(f"Current routing info: {routing_info}")
            return routing_info
        except Exception as e:
            self.logger.exception(f"Error in get_routing_info: {e}")
            return {}

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        dpid = datapath.id

        if not isinstance(dpid, int):
            self.logger.error(f"Invalid dpid: {dpid}")
            return

        if dpid in self.dpidToDatapath:
            self.logger.warning(f"Datapath {dpid} already registered. Updating.")

        self.dpidToDatapath[dpid] = datapath  # تسجيل datapath
        self.last_arrived_package[dpid] = {}  # تهيئة self.last_arrived_package

        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER, ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions)

        match = parser.OFPMatch(eth_type=0x0800, ip_proto=1, icmpv4_type=3)
        actions = []
        self.add_flow(datapath, 1, match, actions)

        if isinstance(self.domain_switches, (list, set)):  # اختصار للتحقق من النوع
            if dpid in self.domain_switches:
                if not self.topology_graph.has_node(dpid):
                    self.topology_graph.add_node(dpid)
                # add initial flows between hosts in same domain
                    if dpid == 1:
                        h1_mac = "00:00:00:00:00:11"
                        h2_mac = "00:00:00:00:00:12"
                        h3_mac = "00:00:00:00:00:13"
                        h1_ip = "10.0.0.11"
                        h2_ip = "10.0.0.12"
                        h3_ip = "10.0.0.13"
                        self.add_initial_flows(datapath, h1_ip, h2_ip, h1_mac, h2_mac)
                        self.add_initial_flows(datapath, h1_ip, h3_ip, h1_mac, h3_mac)
                        self.add_initial_flows(datapath, h2_ip, h1_ip, h2_mac, h1_mac)
                        self.add_initial_flows(datapath, h2_ip, h3_ip, h2_mac, h3_mac)
                        self.add_initial_flows(datapath, h3_ip, h1_ip, h3_mac, h1_mac)
                        self.add_initial_flows(datapath, h3_ip, h2_ip, h3_mac, h2_mac)
    
                    if dpid == 4:
                        h1_mac = "00:00:00:00:00:41"
                        h2_mac = "00:00:00:00:00:42"
                        h3_mac = "00:00:00:00:00:43"
                        h1_ip = "10.0.0.41"
                        h2_ip = "10.0.0.42"
                        h3_ip = "10.0.0.43"

                        self.add_initial_flows(datapath, h1_ip, h2_ip, h1_mac, h2_mac)
                        self.add_initial_flows(datapath, h1_ip, h3_ip, h1_mac, h3_mac)
                        self.add_initial_flows(datapath, h2_ip, h1_ip, h2_mac, h1_mac)
                        self.add_initial_flows(datapath, h2_ip, h3_ip, h2_mac, h3_mac)
                        self.add_initial_flows(datapath, h3_ip, h1_ip, h3_mac, h1_mac)
                        self.add_initial_flows(datapath, h3_ip, h2_ip, h3_mac, h2_mac)
        else:
            self.logger.error("self.domain_switches is not a list or set.")
        self.send_port_stats_request(datapath) # إرسال طلب إحصائيات المنافذ
        hub.spawn(self.monitor_latency, datapath, ofproto)  # بدء مراقبة زمن الوصول
    # Start ARP requests
        if dpid in self.domain_switches:
            hub.spawn(self.send_arp_request, datapath, ofproto)
        
    def add_initial_flows(self, datapath, ip_src, ip_dst, mac_src, mac_dst):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        
        actions = [parser.OFPActionSetField(eth_src=mac_src),
                parser.OFPActionSetField(eth_dst=mac_dst),
                parser.OFPActionOutput(ofproto.OFPP_NORMAL)]  # Use normal output
        
        match = parser.OFPMatch(eth_type=0x0800, ipv4_src=ip_src, ipv4_dst=ip_dst)
        self.add_flow(datapath, 2, match, actions)  # Higher priority for initial flows
    def monitor_sw_controller_latency(self, datapath):
        hub.sleep(0.5 + self.waitTillStart)
        iterator = 0
        while True:
            if iterator % 2 == 0:
                self.send_port_stats_request(datapath)
            else:
                self.send_flow_stats_request(datapath)
            iterator += 1
            hub.sleep(interval_controller_switch_latency)
    def checking_updates(self):
        i = 0
        while not self.latency_measurement_flag:
            self.logger.info("Waiting for latency measurement")
            hub.sleep(1)
        hub.sleep(5)
        while True:
            if self.parent_conn.poll():
                action = self.parent_conn.recv()
                if len(action) > 0:
                    self.logger.info("Received action: %s", action)
                    if self.action_mode.value == ActionMode.ONE_FLOW.value:
                        if "_" in action[0]:
                            action_id_string = action[0]
                            new_path = action[1]
                            self.reroute(action_id_string, new_path)
                            self.logger.info("Rerouted: %s", action_id_string)
                    elif self.action_mode.value == ActionMode.DIRECT_CHANGE.value:
                        if type(action) == dict:
                            for change in action:
                                flow_id = change
                                path = action[flow_id]
                                self.reroute(str(flow_id), path)
                                self.logger.info("Rerouted: %s", flow_id)
                                hub.sleep(0.05)
                    self.last_state_change = time.time() + (Config.delay_reward * interval_communication_processes) - 1
                    self.last_action = time.time()

            self.latency_dict = functions.convert_data_map_to_dict(self.data_map, 'latencyRTT')

            # جمع بيانات عرض النطاق والتدفق
            bw_port_dict = copy.deepcopy(self.bandwith_port_dict)
            bw_flow_dict = copy.deepcopy(self.bandwith_flow_dict)
            
            if i > 0:
                lat_measurements_flag = functions.check_new_measurement(self.last_state_change, self.last_arrived_package)
                if self.iteration_flag or (Config.split_up_load_levels_flag and self.reset_flag):
                    self.logger.info("Resetting routing tables")
                    for flow_id in self.chosen_path_per_flow:
                        src_ip, dst_ip = functions.build_ip_adresses(flow_id)
                        path = self.chosen_path_per_flow[flow_id]
                        for switch in path:
                            try:
                                self.bandwith_flow_dict[switch][src_ip].pop(dst_ip, None)
                            except KeyError:
                                self.logger.error("Key %s not found", dst_ip)
                            self.del_flow_specific_switch(switch, src_ip, dst_ip)
                    self.already_routed_ip.clear()

                if lat_measurements_flag or self.iteration_flag or self.reset_flag:
                    sending_dict = {
                        'currentCombination': self.chosen_path_per_flow,
                        'paths_per_flow': self.paths_per_flows,
                        'latencyDict': self.latency_dict,
                        'resetFlag': self.reset_flag,
                        'loadLevel': self.load_level,
                        'iterationFlag': self.iteration_flag,
                        'iteration': self.iteration,
                        'stopFlag': self.stop_flag,
                        'topology': self.get_domain_topology(),
                        'bwPortDict' : bw_port_dict,
                        'bwFlowDict' : bw_flow_dict
                    }
                    self.logger.info(f"Sending data to learning module: {sending_dict}")
                    self.parent_conn.send(sending_dict)

                    # تفعيل خوارزمية التعلم المعزز هنا
                    if  self.chosen_path_per_flow and Config.qMode.value != QMode.SHORTEST_PATH.value:
                         self.logger.info(f"Sending data to learning module to trigger action choice")
                    if Config.qMode.value == QMode.SHORTEST_PATH.value:
                        self.last_state_change = time.time() + 2.0
                    self.reset_flag = False
                    self.iteration_flag = False
            if i == 3:
                self.latency_dict_SPF = copy.deepcopy(self.latency_dict)
            i = i + 1
            if self.neighbor_controllers:
               for neighbor_id, neighbor_info in self.neighbor_controllers.items():
                  eventlet.greenthread.spawn(self._fetch_routing_info, neighbor_id, neighbor_info)
            hub.sleep(interval_communication_processes)
            

# تعديل في learning_module.py


    def _fetch_routing_info(self, neighbor_id, neighbor_info):
        context = ssl.create_default_context()
        try:
            conn = http.client.HTTPConnection(neighbor_info['ip'], neighbor_info['rest_port'], timeout=10)
            conn.request("GET", "/routing_info")
            response = conn.getresponse()
            if response.status == 200:
                try:
                    routing_info = json.loads(response.read().decode('utf-8'))
                    self.logger.info(f"Received routing info from neighbor {neighbor_id}: {routing_info}")
                    if isinstance(routing_info, dict) and all(isinstance(v, dict) for v in routing_info.values()):
                        self._merge_routing_info(routing_info)
                    else:
                        self.logger.error(f"Invalid routing information format from neighbor {neighbor_id}")
                except json.JSONDecodeError as e:
                    self.logger.error(f"Error decoding JSON from neighbor {neighbor_id}: {e}")
            else:
                self.logger.error(f"Error getting routing info from neighbor {neighbor_id}: {response.status} {response.reason}")
        except (http.client.HTTPException, json.JSONDecodeError, socket.timeout) as e:
            self.logger.error(f"Error getting routing info from neighbor {neighbor_id}: {e}")
            eventlet.sleep(1)
        except socket.error as e:
            self.logger.error(f"Socket error: {e}")
            eventlet.sleep(1)
        finally:
            if conn:
                conn.close()
        hub.sleep(10) # Add a sleep here to reduce requests
    def _merge_routing_info(self, routing_info):
        try:
            self.logger.info(f"Starting merge with routing info: {routing_info}")
            for src_ip, dest_paths in routing_info.items():
                if not isinstance(dest_paths, dict):
                    self.logger.error(f"Invalid dest_paths format for source {src_ip}: Expected dict, got {type(dest_paths)}")
                    continue
                for dst_ip, path in dest_paths.items():
                    if not isinstance(path, list):
                        self.logger.error(f"Invalid path format for source {src_ip} and destination {dst_ip}: Expected list, got {type(path)}")
                        continue
                    if src_ip not in self.paths_per_flows:
                        self.paths_per_flows[src_ip] = defaultdict(set)
                    current_paths = self.paths_per_flows[src_ip][dst_ip]
                    current_paths.update(tuple(p) for p in path)
            current_time = time.time()
            if current_time - self.last_print_time >= 10:
                self.logger.info(f"Successfully merged routing info. New routing table: {self.paths_per_flows}")
                self.last_print_time = current_time
        except KeyError as e:
            self.logger.error(f"KeyError during routing info merge: {e}")
        except Exception as e:
            self.logger.exception(f"An unexpected error occurred during routing info merge: {e}")


    def add_flow(self, datapath, priority, match, actions):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(datapath=datapath, flags=ofproto.OFPFC_ADD, priority=priority, match=match, instructions=inst)
        datapath.send_msg(mod)
        self.logger.info(f"Added flow: priority={priority}, match={match}, actions={actions}")

    def mod_flow(self, datapath, priority, match, actions):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(datapath=datapath, flags=ofproto.OFPFC_MODIFY, priority=priority, match=match, instructions=inst)
        datapath.send_msg(mod)
        self.logger.info(f"Modified flow: priority={priority}, match={match}, actions={actions}")

    def del_flow(self, datapath, match):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        mod = parser.OFPFlowMod(datapath=datapath, command=ofproto.OFPFC_DELETE, out_port=ofproto.OFPP_ANY, out_group=ofproto.OFPG_ANY, match=match)
        datapath.send_msg(mod)
        self.logger.info(f"Deleted flow: match={match}")

    def get_domain_topology(self):
        topology = {
            'nodes': [],
            'links': []
        }
        for node in self.topology_graph.nodes():
            topology['nodes'].append({'id': node})
        for src, dst, data in self.topology_graph.edges(data=True):
            link = {
                'source': src,
                'target': dst,
                'latency': data.get('latency', None)
            }
            topology['links'].append(link)
        self.logger.info(f"Current topology: {topology}")
        return topology

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        timestamp_recieve = time.time()
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        dpid = datapath.id

        try:
            if not isinstance(dpid, int):
                self.logger.error(f"Invalid dpid: {dpid}")
                return

            in_port = msg.match['in_port']
            if not isinstance(in_port, int):
                self.logger.error(f"Invalid in_port: {in_port}")
                return

            pkt = packet.Packet(msg.data)
            eth_pkt = pkt.get_protocols(ethernet.ethernet)[0]
            arp_pkt = pkt.get_protocol(arp.arp)
            ipv4_pkt = pkt.get_protocol(ipv4.ipv4)
            dst_mac = eth_pkt.dst
            src_mac = eth_pkt.src

            if eth_pkt.ethertype == self.PROBE_PACKET_ETHERTYPE:  #  استخدم الثابت المُعرّف
                pkt_header_list = pkt[-1].decode("utf-8").split('#')
                timestamp_sent = float(pkt_header_list[0])
                dpid_sent = int(pkt_header_list[1])
                
                if dpid not in self.data_map:
                   self.data_map[dpid] = {}
                if dpid_sent not in self.data_map[dpid]:
                   self.data_map[dpid][dpid_sent] = {'latencyRTT': []}

                time_difference = timestamp_recieve - timestamp_sent
                if time_difference < 0:
                  self.logger.error(f"Negative time difference detected in _packet_in_handler: {time_difference}")
                  return
                  
                
                latency_link_echo_rtt = time_difference 
                latency_obj_rtt = {'timestamp': timestamp_sent, 'value': latency_link_echo_rtt * 1000}
                self.data_map[dpid][dpid_sent]['latencyRTT'].append(latency_obj_rtt)
                self.last_arrived_package[dpid][dpid_sent] = time.time()
                self.update_topology(dpid, dpid_sent, latency_link_echo_rtt * 1000)
                self.logger.info(f"dpid:{dpid} dpid_sent:{dpid_sent} timestamp_recieve:{timestamp_recieve} timestamp_sent:{timestamp_sent} Calculated latency_link_echo_rtt: {latency_link_echo_rtt}")
                return

            elif arp_pkt:
                src_ip = arp_pkt.src_ip
                dst_ip = arp_pkt.dst_ip
                self.arp_table[src_ip] = src_mac

                if dst_ip in self.arp_table:
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts.get(src_mac)
                    h2 = self.hosts.get(dst_mac)
                    if h1 and h2 and (h1, h2) not in self.already_routed:
                        self.routing_arp(h1, h2, src_ip, dst_ip)
                        self.already_routed.append((h1, h2))
                        return  # لا حاجة للإرسال  out

                else:
                    out_port = ofproto.OFPP_FLOOD
                    actions = [parser.OFPActionOutput(out_port)]
                    data = None
                    if msg.buffer_id == ofproto.OFP_NO_BUFFER:
                       data = msg.data
                    out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port,
                                                actions=actions, data=data)
                    datapath.send_msg(out)

            elif ipv4_pkt:
                src_ip = ipv4_pkt.src
                dst_ip = ipv4_pkt.dst
                if dst_ip in self.arp_table and src_ip in self.arp_table:
                   src_mac = self.arp_table[src_ip]
                   dst_mac = self.arp_table[dst_ip]
                   h1 = self.hosts.get(src_mac)
                   h2 = self.hosts.get(dst_mac)
                   if h1 and h2 and (h1, h2) not in self.already_routed_ip:
                      self.routing_ip(h1, h2, src_ip, dst_ip)
                      self.already_routed_ip.append((h1, h2))
        except Exception as e:
            self.logger.exception(f"Exception in _packet_in_handler: {e}")
    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def port_stats_reply_handler(self, ev):
        current_time = time.time()
        dpid_rec = ev.msg.datapath.id
        body = ev.msg.body

        try:
            old_time = self.rtt_stats_sent[dpid_rec]
            total_rtt = current_time - old_time
            if total_rtt < 0:
                 self.logger.error(f"Negative total_rtt detected in port_stats_reply_handler: {total_rtt}")
                 return
            self.rtt_portStats_to_dpid[dpid_rec] = total_rtt
            self.logger.info(f"Port stats reply received from dpid: {dpid_rec}, rtt: {total_rtt}")
            for statistic in body:
                port_no = int(statistic.port_no)
                if dpid_rec not in self.temp_bw_map_ports:
                            self.temp_bw_map_ports[dpid_rec] = defaultdict(dict)
                            self.bandwith_port_dict[dpid_rec] = {}

                if port_no not in self.temp_bw_map_ports[dpid_rec]:
                    bytes_now = statistic.rx_bytes
                    ts_now = (statistic.duration_sec + statistic.duration_nsec / (10 ** 9))
                    self.temp_bw_map_ports[dpid_rec][port_no]['ts'] = ts_now
                    self.temp_bw_map_ports[dpid_rec][port_no]['bytes'] = bytes_now
                    self.logger.info(f"New values for port {port_no} at switch {dpid_rec}: ts_now={ts_now}, bytes_now={bytes_now}")
                else:
                   ts_before = self.temp_bw_map_ports[dpid_rec][port_no]['ts']
                   bytes_before = self.temp_bw_map_ports[dpid_rec][port_no]['bytes']
                   bytes_now = statistic.tx_bytes
                   ts_now = (statistic.duration_sec + statistic.duration_nsec / (10 ** 9))
                   byte_diff = bytes_now - bytes_before
                   ts_diff = ts_now - ts_before
                   if ts_diff < 0:
                        self.logger.error(f"Negative ts_diff detected in port_stats_reply_handler: {ts_diff}")
                        continue
                   if ts_diff > 0:
                      bw = byte_diff / ts_diff
                      self.bandwith_port_dict[dpid_rec][port_no] = bw
                      self.logger.info(f"Calculated bandwidth for port {port_no} at switch {dpid_rec}: bw={bw}, byte_diff={byte_diff}, ts_diff={ts_diff}")
                   else:
                      self.logger.warning("ts_diff is zero. Bandwidth calculation skipped.")
        except KeyError as e:
            self.logger.error(f"KeyError in port_stats_reply_handler: {e}")
        except Exception as e:
            self.logger.exception(f"Error in port_stats_reply_handler: {e}")

    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def flow_stats_reply_handler(self, ev):
        dpid_rec = ev.msg.datapath.id
        try:
            self.rtt_portStats_to_dpid[dpid_rec] = time.time() - self.rtt_stats_sent[dpid_rec]
            if self.rtt_portStats_to_dpid[dpid_rec] < 0:
                self.logger.error(f"Negative time difference detected in flow_stats_reply_handler: {self.rtt_portStats_to_dpid[dpid_rec]}")
                return
            for statistic in ev.msg.body:
                try:  # try-except داخلي لمعالجة أخطاء في كل إحصائية
                    if 'icmpv4_type' not in statistic.match:
                        ip_src = statistic.match['ipv4_src']
                        ip_dst = statistic.match['ipv4_dst']
                        number_bytes = statistic.byte_count
                        # استخدام defaultdict
                        if dpid_rec not in self.temp_bw_map_flows:
                            self.temp_bw_map_flows[dpid_rec] = defaultdict(lambda: defaultdict(dict))
                        if ip_dst not in self.temp_bw_map_flows[dpid_rec][ip_src]:  # لا حاجة لـ list()
                            ts_now = (statistic.duration_sec + statistic.duration_nsec / (10 ** 9))
                            self.temp_bw_map_flows[dpid_rec][ip_src][ip_dst]['ts'] = ts_now
                            self.temp_bw_map_flows[dpid_rec][ip_src][ip_dst]['bytes'] = number_bytes
                            self.logger.info(f"New values for flow from {ip_src} to {ip_dst} at switch {dpid_rec}: ts_now={ts_now}, bytes_now={number_bytes}")
                        else:
                            ts_now = (statistic.duration_sec + statistic.duration_nsec / (10 ** 9))
                            ts_before = self.temp_bw_map_flows[dpid_rec][ip_src][ip_dst]['ts']
                            bytes_before = self.temp_bw_map_flows[dpid_rec][ip_src][ip_dst]['bytes']

                            time_diff = ts_now - ts_before
                            bytes_diff = number_bytes - bytes_before
                            if time_diff < 0:
                              self.logger.error(f"Negative time_diff detected in flow_stats_reply_handler: {time_diff}")
                              continue
                            if time_diff > 0: # تجنب القسمة على صفر
                                bw = bytes_diff / time_diff
                                #  استخدام defaultdict
                                if dpid_rec not in self.bandwith_flow_dict:
                                    self.bandwith_flow_dict[dpid_rec] = defaultdict(dict)
                                self.bandwith_flow_dict[dpid_rec][ip_src][ip_dst] = bw
                                self.temp_bw_map_flows[dpid_rec][ip_src][ip_dst]['ts'] = ts_now
                                self.temp_bw_map_flows[dpid_rec][ip_src][ip_dst]['bytes'] = number_bytes
                                self.logger.info(f"Calculated bandwidth for flow from {ip_src} to {ip_dst} at switch {dpid_rec}: bw={bw}, byte_diff={bytes_diff}, time_diff={time_diff}")
                            else:
                                self.logger.warning("time_diff is zero. Bandwidth calculation skipped.")
                except KeyError as e:  # معالجة KeyError  بشكل منفصل
                   self.logger.error(f"KeyError processing flow stats: {e}")
                    # إجراء تصحيحي - ربما تجاهل هذه الإحصائية
                   continue
                except Exception as e:
                    self.logger.exception(f"Error processing individual flow stat: {e}") # معلومات أكثر
                    continue
        except KeyError as e:
            self.logger.error(f"KeyError in flow_stats_reply_handler: {e}")
        except Exception as e:
            self.logger.exception(f"Error in flow_stats_reply_handler: {e}")
    def monitor_latency(self, datapath, ofproto):
        hub.sleep(self.waitTillStart + 5)
        self.waitTillStart += 0.1
        print("MONITORING LATENCY STARTED dpid: {}".format(datapath.id))
        self.latency_measurement_flag = True
        while True:
            self.send_packet_out(datapath, ofproto.OFP_NO_BUFFER, ofproto.OFPP_CONTROLLER)
            hub.sleep(interval_update_latency)
    def send_port_stats_request(self, datapath):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        req = ofp_parser.OFPPortStatsRequest(datapath, 0, ofp.OFPP_ANY)
        self.rtt_stats_sent[datapath.id] = time.time()
        datapath.send_msg(req)
    def send_flow_stats_request(self, datapath):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        match = ofp_parser.OFPMatch(eth_type=2048)
        req = ofp_parser.OFPFlowStatsRequest(datapath, 0, ofp.OFPTT_ALL, ofp.OFPP_ANY, ofp.OFPG_ANY, 0, 0, match)
        self.rtt_stats_sent[datapath.id] = time.time()
        datapath.send_msg(req)
    def update_topology(self, dpid_rec, dpid_sent, latency):
        if self.topology_graph.has_edge(dpid_rec, dpid_sent):
           self.topology_graph[dpid_rec][dpid_sent]['latency'] = latency 
        else: 
           self.topology_graph.add_edge(dpid_rec, dpid_sent, latency=latency)
           self.logger.info(f"Updated topology with latency between {dpid_rec} and {dpid_sent}: {latency} ms")
    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def port_stats_reply_handler(self, ev):
        current_time = time.time()
        dpid_rec = ev.msg.datapath.id
        body = ev.msg.body
        try:
            old_time = self.rtt_stats_sent[dpid_rec]
            total_rtt = current_time - old_time
            if total_rtt < 0:
                 self.logger.error(f"Negative total_rtt detected in port_stats_reply_handler: {total_rtt}")
                 return
            self.rtt_portStats_to_dpid[dpid_rec] = total_rtt
            for statistic in body:
                port_no = int(statistic.port_no)
                for dpid_sent, port_data in self.data_map.get(dpid_rec, {}).items():
                    in_port = port_data.get('in_port')
                    if in_port == port_no:
                        if dpid_rec not in self.temp_bw_map_ports:
                            self.temp_bw_map_ports[dpid_rec] = defaultdict(dict)
                            self.bandwith_port_dict[dpid_rec] = {}

                        if port_no not in self.temp_bw_map_ports[dpid_rec]:
                            bytes_now = statistic.rx_bytes
                            ts_now = (statistic.duration_sec + statistic.duration_nsec / (10 ** 9))
                            self.temp_bw_map_ports[dpid_rec][port_no]['ts'] = ts_now
                            self.temp_bw_map_ports[dpid_rec][port_no]['bytes'] = bytes_now
                            self.logger.info(f"New values for port {port_no} at switch {dpid_rec}: ts_now={ts_now}, bytes_now={bytes_now}")
                        else:
                            ts_before = self.temp_bw_map_ports[dpid_rec][port_no]['ts']
                            bytes_before = self.temp_bw_map_ports[dpid_rec][port_no]['bytes']
                            bytes_now = statistic.tx_bytes
                            ts_now = (statistic.duration_sec + statistic.duration_nsec / (10 ** 9))
                            byte_diff = bytes_now - bytes_before
                            ts_diff = ts_now - ts_before
                            if ts_diff < 0:
                                self.logger.error(f"Negative ts_diff detected in port_stats_reply_handler: {ts_diff}")
                                continue
                            if ts_diff > 0:
                                bw = byte_diff / ts_diff
                                self.bandwith_port_dict[dpid_rec][port_no] = bw
                                self.logger.info(f"Calculated bandwidth for port {port_no} at switch {dpid_rec}: bw={bw}, byte_diff={byte_diff}, ts_diff={ts_diff}")
                            else:
                                self.logger.warning("ts_diff is zero. Bandwidth calculation skipped.")
                        break  # الخروج من الحلقة الداخلية بعد إيجاد المنفذ
        except KeyError as e:
            self.logger.error(f"KeyError in port_stats_reply_handler: {e}")
        except Exception as e:
            self.logger.exception(f"Error in port_stats_reply_handler: {e}")
    def send_packet_out(self, datapath, buffer_id, in_port):
        ofp = datapath.ofproto
        ofp_parser = datapath.ofproto_parser
        
        try: # معالجة الأخطاء
            pck = self.create_packet(datapath.id)
            data = pck.data
            actions = [ofp_parser.OFPActionOutput(ofp.OFPP_FLOOD, 0)]
            req = ofp_parser.OFPPacketOut(datapath, buffer_id, in_port, actions, data)
            datapath.send_msg(req)
        except Exception as e:
            self.logger.error(f"Error sending packet out: {e}")
    def create_packet(self, dpid):
        pkt = packet.Packet()
        pkt.add_protocol(ethernet.ethernet(ethertype=0x07c3, dst='ff:ff:ff:ff:ff:ff', src='00:00:00:00:00:09'))
        whole_data = str(time.time()) + '#' + str(dpid) + '#'
        pkt.add_protocol(bytes(whole_data, "utf-8"))
        pkt.serialize()
        return pkt
    def save_in_map(self, dpid_rec, in_port, bw, ts_before):
        try:
            for keys_dpid_sent, values in self.data_map[dpid_rec].items():  #  استخدام .items()
                if values.get('in_port') == in_port:  #  استخدام get()
                    bw_object = {'timestamp': ts_before, 'value': bw / 10**3}
                    if 'bw' not in values: # تحقق من وجود المفتاح 'bw'
                       values['bw'] = []
                    values['bw'].append(bw_object)  # الوصول المباشر إلى values
                    break  # الخروج من الحلقة بعد العثور على المنفذ
        except KeyError as e:
            self.logger.error(f"KeyError in save_in_map: {e}")  #  معالجة KeyError
        except Exception as e: # معالجة أخطاء أخرى
             self.logger.exception(f"Error in save_in_map: {e}")
    def update_paths_per_flows(self, src_ip, dst_ip, path):
        if src_ip not in self.paths_per_flows:
            self.paths_per_flows[src_ip] = defaultdict(set)
        current_paths = self.paths_per_flows[src_ip][dst_ip]
        current_paths.update(tuple(p) for p in path)
        self.logger.info(f"Updated paths_per_flows for {src_ip} -> {dst_ip}: {self.paths_per_flows[src_ip][dst_ip]}")

    
    def send_arp_request(self, datapath, ofproto):
        while True:
            parser = datapath.ofproto_parser
       # Send ARP requests for all IPs in the network
            for i in range(11, 14):
                dst_ip = f'10.0.0.{i}'  # Destination IP for hosts in s1
                self.send_arp(datapath, ofproto, dst_ip, "00:00:00:00:00:09", "10.0.0.1")
            for i in range(41, 44):
                dst_ip = f'10.0.0.{i}' # Destination IP for hosts in s4
                self.send_arp(datapath, ofproto, dst_ip, "00:00:00:00:00:09", "10.0.0.1")
            hub.sleep(10)
    def send_arp(self, datapath, ofproto, dst_ip, src_mac, src_ip):
        parser = datapath.ofproto_parser
        ether_pkt = ethernet.ethernet(ethertype=ether_types.ETH_TYPE_ARP,
                                        dst="ff:ff:ff:ff:ff:ff",
                                       src=src_mac)
        arp_pkt = arp.arp(opcode=arp.ARP_REQUEST,
                         src_mac=src_mac, src_ip=src_ip,
                         dst_mac="00:00:00:00:00:00", dst_ip=dst_ip)

        pkt = packet.Packet()
        pkt.add_protocol(ether_pkt)
        pkt.add_protocol(arp_pkt)
        pkt.serialize()
        actions = [parser.OFPActionOutput(ofproto.OFPP_FLOOD)]
        out = parser.OFPPacketOut(datapath=datapath,
                                 buffer_id=ofproto.OFP_NO_BUFFER, # Set buffer_id
                                 in_port=ofproto.OFPP_ANY,
                                 actions=actions,
                                 data=pkt.data)
        datapath.send_msg(out)
        
    def routing_ip(self, h1, h2, src_ip, dst_ip):
        id_forward = functions.build_connection_between_hosts_id(src_ip, dst_ip)
        if ROUTING_TYPE == RoutingType.DFS:
            try:
                if h1[0] in self.domain_switches and h2[0] in self.domain_switches:
                    path = nx.dijkstra_path(self.topology_graph, h1[0], h2[0], weight='latency')  # Use 'latency'
                    self.routing_shortest_path.install_path(self, path, h1[1], h2[1], src_ip, dst_ip, 'ipv4')
                    self.chosen_path_per_flow[id_forward] = path
                    print(f"Routed flow {id_forward} within domain {self.domain_id}: {path}")
                    self.update_paths_per_flows(src_ip, dst_ip, [path])
                    self.paths_per_flows[id_forward] = [path] # حفظ المسار هنا
                    self.logger.info(f"Routing IP: Path chosen: {path}, paths_per_flows: {self.paths_per_flows}") # تسجيل المسار المختار
                else:
                   shortest_path = None
                   for neighbor_id, neighbor_info in self.neighbor_controllers.items():
                        try:
                            context = ssl._create_default_https_context()
                            conn = http.client.HTTPConnection(neighbor_info['ip'], neighbor_info['rest_port'])
                            conn.request("GET", f"/domain/{neighbor_id}/topology")
                            response = conn.getresponse()
                            if response.status == 200:
                                neighbor_topology = json.loads(response.read().decode())
                                # Merge neighbor's topology with your own
                                for node in neighbor_topology.get('nodes', []):
                                    if not self.topology_graph.has_node(node['id']):
                                        self.topology_graph.add_node(node['id'])
                                for link in neighbor_topology.get('links', []):
                                  source = link.get('source')
                                  target = link.get('target')
                                  if source and target:
                                     if self.topology_graph.has_edge(source, target):
                                        self.topology_graph[source][target]['latency'] = link.get('latency', None)
                                     else:
                                        self.topology_graph.add_edge(source, target, latency=link.get('latency', None))
                                try:
                                   shortest_path = nx.shortest_path(self.topology_graph, source=h1[0], target=h2[0], weight='latency')
                                except nx.NetworkXNoPath:
                                    shortest_path = None

                            else:
                                print(f"Error getting topology from neighbor {neighbor_id}: {response.status} {response.reason}")
                        except Exception as e:
                           print(f"Error getting topology from neighbor {neighbor_id}: {e}")
                           continue
                        finally:
                            if conn:
                                conn.close()
                   if shortest_path:
                       print(f"Inter-domain path found for flow {id_forward}: {shortest_path}")
                       # Implement inter-domain path installation logic here
                       self.paths_per_flows[id_forward] = [shortest_path] # حفظ المسار هنا
                       self.logger.info(f"Routing IP: Inter-domain path chosen: {shortest_path}, paths_per_flows: {self.paths_per_flows}") # تسجيل المسار المختار
                   else:
                       print(f"No inter-domain path found for flow {id_forward}")
            except nx.NetworkXNoPath:
                print(f"No path found between {h1[0]} and {h2[0]}")
    # تعديل في ControllerMain.routing_arp
    def routing_arp(self, h1, h2, src_ip, dst_ip):
        try:
            if not all(isinstance(x, int) for x in h1 + h2):  #  تحقق شامل من h1 و h2
                 self.logger.error(f"Invalid host data: h1={h1}, h2={h2}")
                 return
            self.logger.info("Routing ARP DFS")
            path_optimal, paths = self.routing_shortest_path.get_optimal_path(self.latency_dict, h1[0], h2[0])
            # تحقق مما إذا تم إرجاع مسار
            if path_optimal:
                self.routing_shortest_path.install_path(self, path_optimal, h1[1], h2[1], src_ip, dst_ip, 'arp')
                self.update_paths_per_flows(src_ip, dst_ip, [path_optimal])
                self.paths_per_flows[functions.build_connection_between_hosts_id(src_ip, dst_ip)] = [path_optimal] # حفظ المسار هنا
                self.logger.info(f"Routing ARP: Path chosen: {path_optimal}, paths_per_flows: {self.paths_per_flows}")  # تسجيل المسار المختار
            else:
                self.logger.warning(f"No optimal path found for ARP between {h1[0]} and {h2[0]}")
        except Exception as e:  # مُعالجة الأخطاء
           self.logger.exception(f"Error in routing_arp: {e}")
# تعديل في ControllerMain.routing_ip

    def reroute(self, id_forward, new_path):
        chosenflow_prev = copy.deepcopy(self.chosen_path_per_flow[id_forward])
        src_ip, dst_ip = functions.build_ip_adresses(id_forward)
        self.chosen_path_per_flow[id_forward] = new_path
        i = 0
        flow_add_list = []
        flow_mod_list = []
        flow_delete_list = []
        difference_set = set(chosenflow_prev).difference(new_path)
        if len(difference_set) > 0:
            flow_delete_list = list(difference_set)
        for switch in new_path:
            if switch in chosenflow_prev:
                index_prev = chosenflow_prev.index(switch)
                if i > 0:
                    if new_path[i - 1] == chosenflow_prev[index_prev - 1]:
                        i += 1
                        continue
                    else:
                        if (new_path[i - 1] not in flow_add_list) and ((new_path[i - 1] not in flow_delete_list) and chosenflow_prev[index_prev] not in flow_delete_list):
                            print("Not same: {}".format(switch))
                            flow_mod_list.append(new_path[i - 1])
            else:
                flow_add_list.append(switch)
                index_prev = new_path.index(switch)
                flow_mod_list.append(new_path[index_prev - 1])
            i += 1
        for j in range(0, len(flow_delete_list), 1):
            switch_old_index = chosenflow_prev.index(flow_delete_list[j])
            switch_old_index_prev = switch_old_index - 1
            if chosenflow_prev[switch_old_index_prev] not in flow_delete_list:
                flow_mod_list.append(chosenflow_prev[switch_old_index_prev])
            j += 1
        flow_mod_list = list(dict.fromkeys(flow_mod_list))
        flow_mod_list.reverse()
        for switch in flow_add_list:
            index = new_path.index(switch)
            next_index = index + 1
            if next_index < len(new_path):
                following_switch = new_path[next_index]
                self.add_flow_specific_switch(switch, src_ip, dst_ip, functions.get_output_port(self, switch, following_switch))
        hub.sleep(0.1)
        for switch in flow_mod_list:
            index = new_path.index(switch)
            next_index = index + 1
            if next_index < len(new_path):
                following_switch = new_path[next_index]
                self.mod_flow_specific_switch(switch, src_ip, dst_ip, functions.get_output_port(self, switch, following_switch))
        for switch in flow_delete_list:
            try:
                self.bandwith_flow_dict[switch][src_ip].pop(dst_ip, None)
            except KeyError:
                print("Key {} not found".format(dst_ip))
            self.del_flow_specific_switch(switch, src_ip, dst_ip)
    def add_flow_specific_switch(self, switch, ip_src, ip_dst, out_port):
            if not isinstance(switch, int):
                self.logger.error(f"Invalid switch dpid: {switch}")
                return
            if not isinstance(out_port, int):
                self.logger.error(f"Invalid output port: {out_port}")
                return        
            dp = self.dpidToDatapath.get(switch)  #  استخدم get() فقط
            if dp is None:
                self.logger.error(f"Datapath not found for dpid: {switch}")
                return
            ofp_parser = dp.ofproto_parser  #  استخدم dp التي تم الحصول عليها من get()
            actions = [ofp_parser.OFPActionOutput(out_port)]
            match_ip = ofp_parser.OFPMatch(eth_type=0x0800, ipv4_src=ip_src, ipv4_dst=ip_dst)
            self.add_flow(dp, 1, match_ip, actions)    
    def mod_flow_specific_switch(self, switch, ip_src, ip_dst, out_port):
            if not isinstance(switch, int):
                self.logger.error(f"Invalid switch dpid: {switch}")
                return
            if not isinstance(out_port, int):
                self.logger.error(f"Invalid output port: {out_port}")
                return

            dp = self.dpidToDatapath.get(switch)
            if dp is None:
                self.logger.error(f"Datapath not found for dpid: {switch}")
                return
            ofp_parser = dp.ofproto_parser
            actions = [ofp_parser.OFPActionOutput(out_port)]
            match_ip = ofp_parser.OFPMatch(eth_type=0x0800, ipv4_src=ip_src, ipv4_dst=ip_dst)
            self.mod_flow(dp, 1, match_ip, actions)
    def del_flow_specific_switch(self, switch, ip_src, ip_dst):
            if not isinstance(switch, int):
                self.logger.error(f"Invalid switch dpid: {switch}")
                return
            dp = self.dpidToDatapath.get(switch)
            if dp is None:
                self.logger.error(f"Datapath not found for dpid: {switch}")
                return
            ofp_parser = dp.ofproto_parser
            match_ip = ofp_parser.OFPMatch(eth_type=0x0800, ipv4_src=ip_src, ipv4_dst=ip_dst)
            self.del_flow(dp, match_ip)    
    def rerouting_simulator(self):
            hub.sleep(20)  # التأخير الأولي
            def reroute_task():  # دالة داخلية للـ rerouting task
                while True:  # أو استخدم شرط إيقاف
                    src_ip = "10.0.0.1"
                    dst_ip = "10.0.0.4"
                    id_forward = functions.build_connection_between_hosts_id(src_ip, dst_ip)
                    try:
                        paths = self.paths_per_flows[id_forward]
                        # استثناء إذا لم تكن هناك مسارات متاحة
                        if not paths:
                            self.logger.error(f"No paths available for flow {id_forward}")
                            break  # أو اتخذ إجراء آخر

                        new_path = self.get_random_path(paths, self.chosen_path_per_flow.get(id_forward))

                        if new_path:  # تحقق من أن الدالة get_random_path لم تُرجع None
                           self.reroute(id_forward, new_path)
                        else:
                           self.logger.warning(f"No alternative path found for {id_forward}") # أو استخدم استثناء

                    except KeyError:
                        self.logger.error(f"Flow {id_forward} not found in paths_per_flows")
                        break # أو تعامل مع الخطأ بشكل مختلف


                    hub.sleep(10)

                # اعكس عناوين IP للمحاكاة
                    src_ip, dst_ip = dst_ip, src_ip
                    id_forward = functions.build_connection_between_hosts_id(src_ip, dst_ip)
                    try:
                        paths = self.paths_per_flows[id_forward]

                        # استثناء إذا لم تكن هناك مسارات متاحة
                        if not paths:
                            self.logger.error(f"No paths available for flow {id_forward}")
                            break  # أو اتخذ إجراء آخر

                        new_path = self.get_random_path(paths, self.chosen_path_per_flow.get(id_forward))
                        if new_path:
                            self.reroute(id_forward, new_path)
                        else:
                           self.logger.warning(f"No alternative path found for {id_forward}")

                    except KeyError:
                        self.logger.error(f"Flow {id_forward} not found in paths_per_flows")
                        break
                    hub.sleep(10)
            hub.spawn(reroute_task)  # تشغيل الـ task في سلسلة رسائل منفصلة
    def get_random_path(self, paths_with_cost_forward, chosenflow_prev):
        paths_cleaned = copy.deepcopy(paths_with_cost_forward)
        i = 0
        for path in paths_cleaned:
            if path[0] == chosenflow_prev:
                paths_cleaned.pop(i)
            i += 1
        new_choice = random.choice(paths_cleaned)
        new_path = new_choice[0]
        return new_path
    def reroute_lv(self, src_ip, dst_ip):
        self.logger.info("Rerouting started")
        id_forward = functions.build_connection_between_hosts_id(src_ip, dst_ip)
        paths_with_cost_forward = self.paths_per_flows[id_forward]
        chosenflow_forward = self.chosen_path_per_flow[id_forward]
        paths_cleaned = copy.deepcopy(paths_with_cost_forward)
        i = 0
        for path in paths_cleaned:
            if path[0] == chosenflow_forward:
                paths_cleaned.pop(i)
            i += 1
        new_path = random.choice(paths_cleaned)
        change_list = functions.get_commands_rerouting(copy.deepcopy(chosenflow_forward), new_path[0])
        insert_operation, flow_mod_operations, delete_operation = functions.retrieve_operations(change_list, new_path[0], chosenflow_forward)
        self.logger.info("Insert Operations: {}".format(insert_operation))
        self.logger.info("Mod Operations: {}".format(flow_mod_operations))
        self.logger.info("Delete Operations: {}".format(delete_operation))


# إعداد مستوى التسجيل لإخفاء الرسائل غير المرغوبة



# تعطيل جميع سجلات werkzeug


class SimpleSwitchController(ControllerBase):
    def __init__(self, req, link, data, **config):
        super(SimpleSwitchController, self).__init__(req, link, data, **config)
        self.simple_switch_app = data[simple_switch_instance_name]
        if self.simple_switch_app is None:
            print(f"cannot find the data{simple_switch_instance_name} ")
        else:
            print(f"can find the data{simple_switch_instance_name}.")
    @route('routing', '/routing_info', methods=['GET'])
    def get_routing_info(self, req, **kwargs):
        try:
            routing_info = self.simple_switch_app.get_routing_info()
            # إضافة سجل لعرض البيانات المسترجعة
            self.simple_switch_app.logger.info(f"Routing info retrieved: {routing_info}")
            
            if not routing_info:
                self.simple_switch_app.logger.warning("No routing info available.")

            body = json.dumps(routing_info)
            self.simple_switch_app.logger.info(f"Routing info sent: {routing_info}")
            return Response(response=body, content_type='application/json')
        except Exception as e:
            self.simple_switch_app.logger.exception(f"Error in get_routing_info: {e}")
            return Response(status=500)
    @route('simpleswitch', url, methods=['GET'], )
    def get_param(self, req, **kwargs):
        obj = kwargs["obj"]
        if obj not in dir(self.simple_switch_app):
            return Response(status=404)
        body = json.dumps({obj: getattr(self.simple_switch_app, obj)})
        return Response(response=body, content_type='application/json', charset='UTF-8')
    @route('simpleswitch', url, methods=['PUT'])
    def put_param(self, req, **kwargs):
        response = {}
        obj = kwargs["obj"]
        
        if not hasattr(self.simple_switch_app, obj):
               return Response(status=404)
        try:
            new_value = req.json if req.body else {}
        except ValueError:
            return Response(status=400)
        print("PUT  obj: {} new_value: {}".format(obj, new_value))
        for key in new_value:
            if obj not in dir(self.simple_switch_app):
                return Response(status=404)
            try:
                obj = getattr(self.simple_switch_app, key)
                print("PUT  obj: {} old_value: {} new_value: {}".format(key, obj, new_value[key]))
                setattr(self.simple_switch_app, key, new_value[key])
                response[key] = new_value[key]
            except Exception as e:
                return Response(status=500)
        body = json.dumps(response)
        return Response(response=body, content_type='application/json', charset='UTF-8')
