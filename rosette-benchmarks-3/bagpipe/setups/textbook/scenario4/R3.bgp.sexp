(((interfaces fe-1/2/1 unit 0 description to_R2)
  (interfaces fe-1/2/1 unit 0 family inet address "10.1.0.2/30")
  (interfaces fe-1/2/2 unit 0 description to_R1)
  (interfaces fe-1/2/2 unit 0 family inet address "10.0.0.6/30")
  (interfaces lo0 unit 0 family inet address "192.168.0.3/32")
  (protocols
   ((bgp
     ((group
       int
       ((type internal)
        (local-address "192.168.0.3")
        (neighbor "192.168.0.1" ((export send-static-aggregate)))
        (neighbor "192.168.0.2" ())))))
    (ospf area "0.0.0.0" interface "fe-1/2/2.0")
    (ospf area "0.0.0.0" interface "fe-1/2/1.0")
    (ospf area "0.0.0.0" interface "lo0.0" passive)))
  (policy-options
   ((policy-statement
     send-static-aggregate
     ((from ((protocol static) (protocol aggregate))) (then accept)))))
  (routing-options
   ((static route "172.16.3.16/28" discard)
    (static route "172.16.3.32/28" discard)
    (static route "172.16.3.48/28" discard)
    (static route "172.16.3.64/28" discard)
    (aggregate route "172.16.0.0/16")
    (aggregate route "172.16.3.0/24")
    (router-id "192.168.0.3")
    (autonomous-system 64510)))))