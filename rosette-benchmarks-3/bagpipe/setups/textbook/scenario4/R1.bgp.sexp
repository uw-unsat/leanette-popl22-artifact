(((interfaces fe-1/2/0 unit 0 description to_R2)
  (interfaces fe-1/2/0 unit 0 family inet address "10.0.0.1/30")
  (interfaces fe-1/2/2 unit 0 description to_R3)
  (interfaces fe-1/2/2 unit 0 family inet address "10.0.0.5/30")
  (interfaces fe-1/2/3 unit 0 description to_R4)
  (interfaces fe-1/2/3 unit 0 family inet address "10.1.0.5/30")
  (interfaces fe-1/2/1 unit 0 description to_R5)
  (interfaces fe-1/2/1 unit 0 family inet address "10.0.0.10/30")
  (interfaces lo0 unit 0 family inet address "192.168.0.1/32")
  (protocols
   ((bgp
     ((group
       int
       ((type internal)
        (local-address "192.168.0.1")
        (export adv-statics)
        (export adv-large-aggregates)
        (export adv-small-aggregates)
        (neighbor "192.168.0.2" ())
        (neighbor "192.168.0.3" ())))
      (group
       to_64511
       ((type external)
        (export adv-large-aggregates)
        (neighbor "10.1.0.6" peer-as 64511 ())
        (type external)
        (export adv-small-aggregates)
        (export adv-statics)
        (neighbor "10.0.0.9" peer-as 64512 ())))))
    (ospf area "0.0.0.0" interface "fe-1/2/0.0")
    (ospf area "0.0.0.0" interface "fe-1/2/2.0")
    (ospf area "0.0.0.0" interface "lo0.0" passive)))
  (policy-options
   ((policy-statement
     adv-large-aggregates
     ((term
       between-16-and-18
       ((from ((protocol aggregate) (route-filter "172.16.0.0/16" upto /18)))
        (then reject)))))
    (policy-statement
     adv-small-aggregates
     ((term
       between-19-and-24
       ((from
         ((protocol aggregate)
          (route-filter "172.16.0.0/16" prefix-length-range /19-/24)))))))
    (policy-statement
     adv-statics
     ((term statics ((from ((protocol static))) (then reject)))))))
  (routing-options
   ((static route "172.16.1.16/28" discard)
    (static route "172.16.1.32/28" discard)
    (static route "172.16.1.48/28" discard)
    (static route "172.16.1.64/28" discard)
    (aggregate route "172.16.0.0/16")
    (aggregate route "172.16.1.0/24")
    (router-id "192.168.0.1")
    (autonomous-system 64510)))))