# xrun.log
```
UVM_INFO @ 0: reporter [RNTST] Running test base_test...
UVM_INFO my_env.sv(16) @ 0: uvm_test_top.env [my_env] my_envs is new
UVM_INFO my_env.sv(21) @ 0: uvm_test_top.env [my_env] my_env build phase!!
UVM_INFO my_model.sv(14) @ 0: uvm_test_top.env.mdl [my_model] my_model is new
UVM_INFO my_agent.sv(24) @ 0: uvm_test_top.env.i_agt [my_agent] my_agent is new (active)
UVM_INFO my_driver.sv(9) @ 0: uvm_test_top.env.i_agt.drv [my_driver] new is called
UVM_INFO my_driver.sv(17) @ 0: uvm_test_top.env.i_agt.drv [my_driver] build_phase is called
UVM_INFO my_driver.sv(21) @ 0: uvm_test_top.env.i_agt.drv [my_driver] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.env.i_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_model.sv(19) @ 0: uvm_test_top.env.mdl [my_model] main_phase is called
UVM_INFO my_agent.sv(26) @ 0: uvm_test_top.env.o_agt [my_agent] my_agent is new (passive)
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.env.o_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.env.o_agt.mon [my_monitor] main_phase is called
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.env.i_agt.mon [my_monitor] main_phase is called
UVM_INFO my_sequence.sv(14) @ 0: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 1
UVM_INFO my_driver.sv(43) @ 1100000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @4985
  dmac                         integral        48    'h78d4a4f4ca65
  smac                         integral        48    'h14335e245f58
  ether_type                   integral        16    'h9c5f
  pload                        da(integral)    1282  -
    [0]                        integral        8     'h7
    [1]                        integral        8     'h16
    [2]                        integral        8     'h22
    [3]                        integral        8     'h4b
    [4]                        integral        8     'h63
    ...                        ...             ...   ...
    [1277]                     integral        8     'hb7
    [1278]                     integral        8     'h8b
    [1279]                     integral        8     'he6
    [1280]                     integral        8     'hd9
    [1281]                     integral        8     'h23
  crc                          integral        32    'h0
  begin_time                   time            64    1100000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 2500000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 2700000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 262300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 262300000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 2
UVM_INFO my_driver.sv(43) @ 262300000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'h49707abd745
  smac                         integral        48    'hbf2875dc1e8c
  ether_type                   integral        16    'hfb9d
  pload                        da(integral)    484   -
    [0]                        integral        8     'h55
    [1]                        integral        8     'he8
    [2]                        integral        8     'h6e
    [3]                        integral        8     'hd8
    [4]                        integral        8     'hea
    ...                        ...             ...   ...
    [479]                      integral        8     'hb8
    [480]                      integral        8     'h53
    [481]                      integral        8     'hc1
    [482]                      integral        8     'h20
    [483]                      integral        8     'hc7
  crc                          integral        32    'h0
  begin_time                   time            64    262300000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 262500000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4974
  dmac        integral        48    'h78d4a4f4ca65
  smac        integral        48    'h14335e245f58
  ether_type  integral        16    'h9c5f
  pload       da(integral)    1282  -
    [0]       integral        8     'h7
    [1]       integral        8     'h16
    [2]       integral        8     'h22
    [3]       integral        8     'h4b
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1277]    integral        8     'hb7
    [1278]    integral        8     'h8b
    [1279]    integral        8     'he6
    [1280]    integral        8     'hd9
    [1281]    integral        8     'h23
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 262500000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5053
  dmac        integral        48    'h78d4a4f4ca65
  smac        integral        48    'h14335e245f58
  ether_type  integral        16    'h9c5f
  pload       da(integral)    1282  -
    [0]       integral        8     'h7
    [1]       integral        8     'h16
    [2]       integral        8     'h22
    [3]       integral        8     'h4b
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1277]    integral        8     'hb7
    [1278]    integral        8     'h8b
    [1279]    integral        8     'he6
    [1280]    integral        8     'hd9
    [1281]    integral        8     'h23
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 262700000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4941
  dmac        integral        48    'h78d4a4f4ca65
  smac        integral        48    'h14335e245f58
  ether_type  integral        16    'h9c5f
  pload       da(integral)    1282  -
    [0]       integral        8     'h7
    [1]       integral        8     'h16
    [2]       integral        8     'h22
    [3]       integral        8     'h4b
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1277]    integral        8     'hb7
    [1278]    integral        8     'h8b
    [1279]    integral        8     'he6
    [1280]    integral        8     'hd9
    [1281]    integral        8     'h23
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 262700000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4941
  dmac        integral        48    'h78d4a4f4ca65
  smac        integral        48    'h14335e245f58
  ether_type  integral        16    'h9c5f
  pload       da(integral)    1282  -
    [0]       integral        8     'h7
    [1]       integral        8     'h16
    [2]       integral        8     'h22
    [3]       integral        8     'h4b
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1277]    integral        8     'hb7
    [1278]    integral        8     'h8b
    [1279]    integral        8     'he6
    [1280]    integral        8     'hd9
    [1281]    integral        8     'h23
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 263700000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 263900000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 363900000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 363900000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 3
UVM_INFO my_driver.sv(43) @ 363900000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5096
  dmac                         integral        48    'hca9a65da67f9
  smac                         integral        48    'he7de7e5a314e
  ether_type                   integral        16    'h1184
  pload                        da(integral)    205   -
    [0]                        integral        8     'h20
    [1]                        integral        8     'hc1
    [2]                        integral        8     'h7b
    [3]                        integral        8     'he5
    [4]                        integral        8     'hd3
    ...                        ...             ...   ...
    [200]                      integral        8     'hf
    [201]                      integral        8     'h41
    [202]                      integral        8     'h6c
    [203]                      integral        8     'h27
    [204]                      integral        8     'he1
  crc                          integral        32    'h0
  begin_time                   time            64    363900000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 364100000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4966
  dmac        integral        48    'h49707abd745
  smac        integral        48    'hbf2875dc1e8c
  ether_type  integral        16    'hfb9d
  pload       da(integral)    484   -
    [0]       integral        8     'h55
    [1]       integral        8     'he8
    [2]       integral        8     'h6e
    [3]       integral        8     'hd8
    [4]       integral        8     'hea
    ...       ...             ...   ...
    [479]     integral        8     'hb8
    [480]     integral        8     'h53
    [481]     integral        8     'hc1
    [482]     integral        8     'h20
    [483]     integral        8     'hc7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 364100000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4973
  dmac        integral        48    'h49707abd745
  smac        integral        48    'hbf2875dc1e8c
  ether_type  integral        16    'hfb9d
  pload       da(integral)    484   -
    [0]       integral        8     'h55
    [1]       integral        8     'he8
    [2]       integral        8     'h6e
    [3]       integral        8     'hd8
    [4]       integral        8     'hea
    ...       ...             ...   ...
    [479]     integral        8     'hb8
    [480]     integral        8     'h53
    [481]     integral        8     'hc1
    [482]     integral        8     'h20
    [483]     integral        8     'hc7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 364300000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4950
  dmac        integral        48    'h49707abd745
  smac        integral        48    'hbf2875dc1e8c
  ether_type  integral        16    'hfb9d
  pload       da(integral)    484   -
    [0]       integral        8     'h55
    [1]       integral        8     'he8
    [2]       integral        8     'h6e
    [3]       integral        8     'hd8
    [4]       integral        8     'hea
    ...       ...             ...   ...
    [479]     integral        8     'hb8
    [480]     integral        8     'h53
    [481]     integral        8     'hc1
    [482]     integral        8     'h20
    [483]     integral        8     'hc7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 364300000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4950
  dmac        integral        48    'h49707abd745
  smac        integral        48    'hbf2875dc1e8c
  ether_type  integral        16    'hfb9d
  pload       da(integral)    484   -
    [0]       integral        8     'h55
    [1]       integral        8     'he8
    [2]       integral        8     'h6e
    [3]       integral        8     'hd8
    [4]       integral        8     'hea
    ...       ...             ...   ...
    [479]     integral        8     'hb8
    [480]     integral        8     'h53
    [481]     integral        8     'hc1
    [482]     integral        8     'h20
    [483]     integral        8     'hc7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 365300000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 365500000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 409700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 409700000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 4
UVM_INFO my_driver.sv(43) @ 409700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'h865358bf5a8f
  smac                         integral        48    'h35d7f98a4d05
  ether_type                   integral        16    'h9b8d
  pload                        da(integral)    1481  -
    [0]                        integral        8     'h5c
    [1]                        integral        8     'hf4
    [2]                        integral        8     'h3d
    [3]                        integral        8     'hdc
    [4]                        integral        8     'hf1
    ...                        ...             ...   ...
    [1476]                     integral        8     'hbe
    [1477]                     integral        8     'h81
    [1478]                     integral        8     'h11
    [1479]                     integral        8     'h7d
    [1480]                     integral        8     'ha3
  crc                          integral        32    'h0
  begin_time                   time            64    409700000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 409900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5080
  dmac        integral        48    'hca9a65da67f9
  smac        integral        48    'he7de7e5a314e
  ether_type  integral        16    'h1184
  pload       da(integral)    205   -
    [0]       integral        8     'h20
    [1]       integral        8     'hc1
    [2]       integral        8     'h7b
    [3]       integral        8     'he5
    [4]       integral        8     'hd3
    ...       ...             ...   ...
    [200]     integral        8     'hf
    [201]     integral        8     'h41
    [202]     integral        8     'h6c
    [203]     integral        8     'h27
    [204]     integral        8     'he1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 409900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4975
  dmac        integral        48    'hca9a65da67f9
  smac        integral        48    'he7de7e5a314e
  ether_type  integral        16    'h1184
  pload       da(integral)    205   -
    [0]       integral        8     'h20
    [1]       integral        8     'hc1
    [2]       integral        8     'h7b
    [3]       integral        8     'he5
    [4]       integral        8     'hd3
    ...       ...             ...   ...
    [200]     integral        8     'hf
    [201]     integral        8     'h41
    [202]     integral        8     'h6c
    [203]     integral        8     'h27
    [204]     integral        8     'he1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 410100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5073
  dmac        integral        48    'hca9a65da67f9
  smac        integral        48    'he7de7e5a314e
  ether_type  integral        16    'h1184
  pload       da(integral)    205   -
    [0]       integral        8     'h20
    [1]       integral        8     'hc1
    [2]       integral        8     'h7b
    [3]       integral        8     'he5
    [4]       integral        8     'hd3
    ...       ...             ...   ...
    [200]     integral        8     'hf
    [201]     integral        8     'h41
    [202]     integral        8     'h6c
    [203]     integral        8     'h27
    [204]     integral        8     'he1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 410100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5073
  dmac        integral        48    'hca9a65da67f9
  smac        integral        48    'he7de7e5a314e
  ether_type  integral        16    'h1184
  pload       da(integral)    205   -
    [0]       integral        8     'h20
    [1]       integral        8     'hc1
    [2]       integral        8     'h7b
    [3]       integral        8     'he5
    [4]       integral        8     'hd3
    ...       ...             ...   ...
    [200]     integral        8     'hf
    [201]     integral        8     'h41
    [202]     integral        8     'h6c
    [203]     integral        8     'h27
    [204]     integral        8     'he1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 411100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 411300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 710700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 710700000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 5
UVM_INFO my_driver.sv(43) @ 710700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5096
  dmac                         integral        48    'h91923b5f5bf8
  smac                         integral        48    'h84bf4ca17bc6
  ether_type                   integral        16    'h8a61
  pload                        da(integral)    1227  -
    [0]                        integral        8     'hdf
    [1]                        integral        8     'hae
    [2]                        integral        8     'h82
    [3]                        integral        8     'h8e
    [4]                        integral        8     'h3c
    ...                        ...             ...   ...
    [1222]                     integral        8     'h91
    [1223]                     integral        8     'h3
    [1224]                     integral        8     'h5a
    [1225]                     integral        8     'h20
    [1226]                     integral        8     'h82
  crc                          integral        32    'h0
  begin_time                   time            64    710700000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 710900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5030
  dmac        integral        48    'h865358bf5a8f
  smac        integral        48    'h35d7f98a4d05
  ether_type  integral        16    'h9b8d
  pload       da(integral)    1481  -
    [0]       integral        8     'h5c
    [1]       integral        8     'hf4
    [2]       integral        8     'h3d
    [3]       integral        8     'hdc
    [4]       integral        8     'hf1
    ...       ...             ...   ...
    [1476]    integral        8     'hbe
    [1477]    integral        8     'h81
    [1478]    integral        8     'h11
    [1479]    integral        8     'h7d
    [1480]    integral        8     'ha3
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 710900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5054
  dmac        integral        48    'h865358bf5a8f
  smac        integral        48    'h35d7f98a4d05
  ether_type  integral        16    'h9b8d
  pload       da(integral)    1481  -
    [0]       integral        8     'h5c
    [1]       integral        8     'hf4
    [2]       integral        8     'h3d
    [3]       integral        8     'hdc
    [4]       integral        8     'hf1
    ...       ...             ...   ...
    [1476]    integral        8     'hbe
    [1477]    integral        8     'h81
    [1478]    integral        8     'h11
    [1479]    integral        8     'h7d
    [1480]    integral        8     'ha3
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 711100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5117
  dmac        integral        48    'h865358bf5a8f
  smac        integral        48    'h35d7f98a4d05
  ether_type  integral        16    'h9b8d
  pload       da(integral)    1481  -
    [0]       integral        8     'h5c
    [1]       integral        8     'hf4
    [2]       integral        8     'h3d
    [3]       integral        8     'hdc
    [4]       integral        8     'hf1
    ...       ...             ...   ...
    [1476]    integral        8     'hbe
    [1477]    integral        8     'h81
    [1478]    integral        8     'h11
    [1479]    integral        8     'h7d
    [1480]    integral        8     'ha3
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 711100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5117
  dmac        integral        48    'h865358bf5a8f
  smac        integral        48    'h35d7f98a4d05
  ether_type  integral        16    'h9b8d
  pload       da(integral)    1481  -
    [0]       integral        8     'h5c
    [1]       integral        8     'hf4
    [2]       integral        8     'h3d
    [3]       integral        8     'hdc
    [4]       integral        8     'hf1
    ...       ...             ...   ...
    [1476]    integral        8     'hbe
    [1477]    integral        8     'h81
    [1478]    integral        8     'h11
    [1479]    integral        8     'h7d
    [1480]    integral        8     'ha3
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 712100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 712300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 960900000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 960900000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 6
UVM_INFO my_driver.sv(43) @ 960900000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'h85f08eab247
  smac                         integral        48    'h756151451d32
  ether_type                   integral        16    'hd5c7
  pload                        da(integral)    1154  -
    [0]                        integral        8     'hdd
    [1]                        integral        8     'hf7
    [2]                        integral        8     'h10
    [3]                        integral        8     'ha5
    [4]                        integral        8     'h63
    ...                        ...             ...   ...
    [1149]                     integral        8     'h3
    [1150]                     integral        8     'hd0
    [1151]                     integral        8     'h95
    [1152]                     integral        8     'h6a
    [1153]                     integral        8     'h64
  crc                          integral        32    'h0
  begin_time                   time            64    960900000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 961100000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5026
  dmac        integral        48    'h91923b5f5bf8
  smac        integral        48    'h84bf4ca17bc6
  ether_type  integral        16    'h8a61
  pload       da(integral)    1227  -
    [0]       integral        8     'hdf
    [1]       integral        8     'hae
    [2]       integral        8     'h82
    [3]       integral        8     'h8e
    [4]       integral        8     'h3c
    ...       ...             ...   ...
    [1222]    integral        8     'h91
    [1223]    integral        8     'h3
    [1224]    integral        8     'h5a
    [1225]    integral        8     'h20
    [1226]    integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 961100000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5011
  dmac        integral        48    'h91923b5f5bf8
  smac        integral        48    'h84bf4ca17bc6
  ether_type  integral        16    'h8a61
  pload       da(integral)    1227  -
    [0]       integral        8     'hdf
    [1]       integral        8     'hae
    [2]       integral        8     'h82
    [3]       integral        8     'h8e
    [4]       integral        8     'h3c
    ...       ...             ...   ...
    [1222]    integral        8     'h91
    [1223]    integral        8     'h3
    [1224]    integral        8     'h5a
    [1225]    integral        8     'h20
    [1226]    integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 961300000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5128
  dmac        integral        48    'h91923b5f5bf8
  smac        integral        48    'h84bf4ca17bc6
  ether_type  integral        16    'h8a61
  pload       da(integral)    1227  -
    [0]       integral        8     'hdf
    [1]       integral        8     'hae
    [2]       integral        8     'h82
    [3]       integral        8     'h8e
    [4]       integral        8     'h3c
    ...       ...             ...   ...
    [1222]    integral        8     'h91
    [1223]    integral        8     'h3
    [1224]    integral        8     'h5a
    [1225]    integral        8     'h20
    [1226]    integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 961300000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5128
  dmac        integral        48    'h91923b5f5bf8
  smac        integral        48    'h84bf4ca17bc6
  ether_type  integral        16    'h8a61
  pload       da(integral)    1227  -
    [0]       integral        8     'hdf
    [1]       integral        8     'hae
    [2]       integral        8     'h82
    [3]       integral        8     'h8e
    [4]       integral        8     'h3c
    ...       ...             ...   ...
    [1222]    integral        8     'h91
    [1223]    integral        8     'h3
    [1224]    integral        8     'h5a
    [1225]    integral        8     'h20
    [1226]    integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 962300000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 962500000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1196500000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 1196500000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 7
UVM_INFO my_driver.sv(43) @ 1196500000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5096
  dmac                         integral        48    'hd573cd1dd27e
  smac                         integral        48    'h8491205471cb
  ether_type                   integral        16    'hcf9b
  pload                        da(integral)    1263  -
    [0]                        integral        8     'h90
    [1]                        integral        8     'h4e
    [2]                        integral        8     'h25
    [3]                        integral        8     'he5
    [4]                        integral        8     'h9d
    ...                        ...             ...   ...
    [1258]                     integral        8     'h98
    [1259]                     integral        8     'hb5
    [1260]                     integral        8     'haa
    [1261]                     integral        8     'h53
    [1262]                     integral        8     'h97
  crc                          integral        32    'h0
  begin_time                   time            64    1196500000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1196700000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5007
  dmac        integral        48    'h85f08eab247
  smac        integral        48    'h756151451d32
  ether_type  integral        16    'hd5c7
  pload       da(integral)    1154  -
    [0]       integral        8     'hdd
    [1]       integral        8     'hf7
    [2]       integral        8     'h10
    [3]       integral        8     'ha5
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1149]    integral        8     'h3
    [1150]    integral        8     'hd0
    [1151]    integral        8     'h95
    [1152]    integral        8     'h6a
    [1153]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1196700000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5062
  dmac        integral        48    'h85f08eab247
  smac        integral        48    'h756151451d32
  ether_type  integral        16    'hd5c7
  pload       da(integral)    1154  -
    [0]       integral        8     'hdd
    [1]       integral        8     'hf7
    [2]       integral        8     'h10
    [3]       integral        8     'ha5
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1149]    integral        8     'h3
    [1150]    integral        8     'hd0
    [1151]    integral        8     'h95
    [1152]    integral        8     'h6a
    [1153]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1196900000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5092
  dmac        integral        48    'h85f08eab247
  smac        integral        48    'h756151451d32
  ether_type  integral        16    'hd5c7
  pload       da(integral)    1154  -
    [0]       integral        8     'hdd
    [1]       integral        8     'hf7
    [2]       integral        8     'h10
    [3]       integral        8     'ha5
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1149]    integral        8     'h3
    [1150]    integral        8     'hd0
    [1151]    integral        8     'h95
    [1152]    integral        8     'h6a
    [1153]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1196900000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5092
  dmac        integral        48    'h85f08eab247
  smac        integral        48    'h756151451d32
  ether_type  integral        16    'hd5c7
  pload       da(integral)    1154  -
    [0]       integral        8     'hdd
    [1]       integral        8     'hf7
    [2]       integral        8     'h10
    [3]       integral        8     'ha5
    [4]       integral        8     'h63
    ...       ...             ...   ...
    [1149]    integral        8     'h3
    [1150]    integral        8     'hd0
    [1151]    integral        8     'h95
    [1152]    integral        8     'h6a
    [1153]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1197900000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1198100000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1453900000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 1453900000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 8
UVM_INFO my_driver.sv(43) @ 1453900000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'h26021cd6357b
  smac                         integral        48    'h2234a9fe84bf
  ether_type                   integral        16    'hde84
  pload                        da(integral)    290   -
    [0]                        integral        8     'h8a
    [1]                        integral        8     'hb4
    [2]                        integral        8     'hcb
    [3]                        integral        8     'h63
    [4]                        integral        8     'hd1
    ...                        ...             ...   ...
    [285]                      integral        8     'hae
    [286]                      integral        8     'hea
    [287]                      integral        8     'h92
    [288]                      integral        8     'h60
    [289]                      integral        8     'h9d
  crc                          integral        32    'h0
  begin_time                   time            64    1453900000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1454100000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5023
  dmac        integral        48    'hd573cd1dd27e
  smac        integral        48    'h8491205471cb
  ether_type  integral        16    'hcf9b
  pload       da(integral)    1263  -
    [0]       integral        8     'h90
    [1]       integral        8     'h4e
    [2]       integral        8     'h25
    [3]       integral        8     'he5
    [4]       integral        8     'h9d
    ...       ...             ...   ...
    [1258]    integral        8     'h98
    [1259]    integral        8     'hb5
    [1260]    integral        8     'haa
    [1261]    integral        8     'h53
    [1262]    integral        8     'h97
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1454100000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5015
  dmac        integral        48    'hd573cd1dd27e
  smac        integral        48    'h8491205471cb
  ether_type  integral        16    'hcf9b
  pload       da(integral)    1263  -
    [0]       integral        8     'h90
    [1]       integral        8     'h4e
    [2]       integral        8     'h25
    [3]       integral        8     'he5
    [4]       integral        8     'h9d
    ...       ...             ...   ...
    [1258]    integral        8     'h98
    [1259]    integral        8     'hb5
    [1260]    integral        8     'haa
    [1261]    integral        8     'h53
    [1262]    integral        8     'h97
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1454300000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5134
  dmac        integral        48    'hd573cd1dd27e
  smac        integral        48    'h8491205471cb
  ether_type  integral        16    'hcf9b
  pload       da(integral)    1263  -
    [0]       integral        8     'h90
    [1]       integral        8     'h4e
    [2]       integral        8     'h25
    [3]       integral        8     'he5
    [4]       integral        8     'h9d
    ...       ...             ...   ...
    [1258]    integral        8     'h98
    [1259]    integral        8     'hb5
    [1260]    integral        8     'haa
    [1261]    integral        8     'h53
    [1262]    integral        8     'h97
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1454300000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5134
  dmac        integral        48    'hd573cd1dd27e
  smac        integral        48    'h8491205471cb
  ether_type  integral        16    'hcf9b
  pload       da(integral)    1263  -
    [0]       integral        8     'h90
    [1]       integral        8     'h4e
    [2]       integral        8     'h25
    [3]       integral        8     'he5
    [4]       integral        8     'h9d
    ...       ...             ...   ...
    [1258]    integral        8     'h98
    [1259]    integral        8     'hb5
    [1260]    integral        8     'haa
    [1261]    integral        8     'h53
    [1262]    integral        8     'h97
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1455300000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1455500000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1516700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 1516700000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 9
UVM_INFO my_driver.sv(43) @ 1516700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5096
  dmac                         integral        48    'h9851b5819a5
  smac                         integral        48    'haf1fee4d4d3e
  ether_type                   integral        16    'h4ebb
  pload                        da(integral)    1416  -
    [0]                        integral        8     'he4
    [1]                        integral        8     'hcd
    [2]                        integral        8     'h3
    [3]                        integral        8     'h6a
    [4]                        integral        8     'h52
    ...                        ...             ...   ...
    [1411]                     integral        8     'h2c
    [1412]                     integral        8     'h5c
    [1413]                     integral        8     'hab
    [1414]                     integral        8     'h6
    [1415]                     integral        8     'h6d
  crc                          integral        32    'h0
  begin_time                   time            64    1516700000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1516900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5036
  dmac        integral        48    'h26021cd6357b
  smac        integral        48    'h2234a9fe84bf
  ether_type  integral        16    'hde84
  pload       da(integral)    290   -
    [0]       integral        8     'h8a
    [1]       integral        8     'hb4
    [2]       integral        8     'hcb
    [3]       integral        8     'h63
    [4]       integral        8     'hd1
    ...       ...             ...   ...
    [285]     integral        8     'hae
    [286]     integral        8     'hea
    [287]     integral        8     'h92
    [288]     integral        8     'h60
    [289]     integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1516900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5042
  dmac        integral        48    'h26021cd6357b
  smac        integral        48    'h2234a9fe84bf
  ether_type  integral        16    'hde84
  pload       da(integral)    290   -
    [0]       integral        8     'h8a
    [1]       integral        8     'hb4
    [2]       integral        8     'hcb
    [3]       integral        8     'h63
    [4]       integral        8     'hd1
    ...       ...             ...   ...
    [285]     integral        8     'hae
    [286]     integral        8     'hea
    [287]     integral        8     'h92
    [288]     integral        8     'h60
    [289]     integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1517100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'h26021cd6357b
  smac        integral        48    'h2234a9fe84bf
  ether_type  integral        16    'hde84
  pload       da(integral)    290   -
    [0]       integral        8     'h8a
    [1]       integral        8     'hb4
    [2]       integral        8     'hcb
    [3]       integral        8     'h63
    [4]       integral        8     'hd1
    ...       ...             ...   ...
    [285]     integral        8     'hae
    [286]     integral        8     'hea
    [287]     integral        8     'h92
    [288]     integral        8     'h60
    [289]     integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1517100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'h26021cd6357b
  smac        integral        48    'h2234a9fe84bf
  ether_type  integral        16    'hde84
  pload       da(integral)    290   -
    [0]       integral        8     'h8a
    [1]       integral        8     'hb4
    [2]       integral        8     'hcb
    [3]       integral        8     'h63
    [4]       integral        8     'hd1
    ...       ...             ...   ...
    [285]     integral        8     'hae
    [286]     integral        8     'hea
    [287]     integral        8     'h92
    [288]     integral        8     'h60
    [289]     integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1518100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1518300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1804700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(14) @ 1804700000: uvm_test_top.env.i_agt.sqr@@my_sequence [my_sequence] transaction: 10
UVM_INFO my_driver.sv(43) @ 1804700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'h141e4ea5b15f
  smac                         integral        48    'hbe71c4a7f69f
  ether_type                   integral        16    'h1086
  pload                        da(integral)    628   -
    [0]                        integral        8     'h1b
    [1]                        integral        8     'h67
    [2]                        integral        8     'hfd
    [3]                        integral        8     'h35
    [4]                        integral        8     'h71
    ...                        ...             ...   ...
    [623]                      integral        8     'hcb
    [624]                      integral        8     'h55
    [625]                      integral        8     'h49
    [626]                      integral        8     'hf0
    [627]                      integral        8     'h8c
  crc                          integral        32    'h0
  begin_time                   time            64    1804700000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          38    uvm_test_top.env.i_agt.sqr.my_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
-------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1804900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5125
  dmac        integral        48    'h9851b5819a5
  smac        integral        48    'haf1fee4d4d3e
  ether_type  integral        16    'h4ebb
  pload       da(integral)    1416  -
    [0]       integral        8     'he4
    [1]       integral        8     'hcd
    [2]       integral        8     'h3
    [3]       integral        8     'h6a
    [4]       integral        8     'h52
    ...       ...             ...   ...
    [1411]    integral        8     'h2c
    [1412]    integral        8     'h5c
    [1413]    integral        8     'hab
    [1414]    integral        8     'h6
    [1415]    integral        8     'h6d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1804900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5047
  dmac        integral        48    'h9851b5819a5
  smac        integral        48    'haf1fee4d4d3e
  ether_type  integral        16    'h4ebb
  pload       da(integral)    1416  -
    [0]       integral        8     'he4
    [1]       integral        8     'hcd
    [2]       integral        8     'h3
    [3]       integral        8     'h6a
    [4]       integral        8     'h52
    ...       ...             ...   ...
    [1411]    integral        8     'h2c
    [1412]    integral        8     'h5c
    [1413]    integral        8     'hab
    [1414]    integral        8     'h6
    [1415]    integral        8     'h6d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1805100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5006
  dmac        integral        48    'h9851b5819a5
  smac        integral        48    'haf1fee4d4d3e
  ether_type  integral        16    'h4ebb
  pload       da(integral)    1416  -
    [0]       integral        8     'he4
    [1]       integral        8     'hcd
    [2]       integral        8     'h3
    [3]       integral        8     'h6a
    [4]       integral        8     'h52
    ...       ...             ...   ...
    [1411]    integral        8     'h2c
    [1412]    integral        8     'h5c
    [1413]    integral        8     'hab
    [1414]    integral        8     'h6
    [1415]    integral        8     'h6d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1805100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5006
  dmac        integral        48    'h9851b5819a5
  smac        integral        48    'haf1fee4d4d3e
  ether_type  integral        16    'h4ebb
  pload       da(integral)    1416  -
    [0]       integral        8     'he4
    [1]       integral        8     'hcd
    [2]       integral        8     'h3
    [3]       integral        8     'h6a
    [4]       integral        8     'h52
    ...       ...             ...   ...
    [1411]    integral        8     'h2c
    [1412]    integral        8     'h5c
    [1413]    integral        8     'hab
    [1414]    integral        8     'h6
    [1415]    integral        8     'h6d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1806100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1806300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1935100000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(63) @ 1935300000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4965
  dmac        integral        48    'h141e4ea5b15f
  smac        integral        48    'hbe71c4a7f69f
  ether_type  integral        16    'h1086
  pload       da(integral)    628   -
    [0]       integral        8     'h1b
    [1]       integral        8     'h67
    [2]       integral        8     'hfd
    [3]       integral        8     'h35
    [4]       integral        8     'h71
    ...       ...             ...   ...
    [623]     integral        8     'hcb
    [624]     integral        8     'h55
    [625]     integral        8     'h49
    [626]     integral        8     'hf0
    [627]     integral        8     'h8c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1935300000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5084
  dmac        integral        48    'h141e4ea5b15f
  smac        integral        48    'hbe71c4a7f69f
  ether_type  integral        16    'h1086
  pload       da(integral)    628   -
    [0]       integral        8     'h1b
    [1]       integral        8     'h67
    [2]       integral        8     'hfd
    [3]       integral        8     'h35
    [4]       integral        8     'h71
    ...       ...             ...   ...
    [623]     integral        8     'hcb
    [624]     integral        8     'h55
    [625]     integral        8     'h49
    [626]     integral        8     'hf0
    [627]     integral        8     'h8c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1935500000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5027
  dmac        integral        48    'h141e4ea5b15f
  smac        integral        48    'hbe71c4a7f69f
  ether_type  integral        16    'h1086
  pload       da(integral)    628   -
    [0]       integral        8     'h1b
    [1]       integral        8     'h67
    [2]       integral        8     'hfd
    [3]       integral        8     'h35
    [4]       integral        8     'h71
    ...       ...             ...   ...
    [623]     integral        8     'hcb
    [624]     integral        8     'h55
    [625]     integral        8     'h49
    [626]     integral        8     'hf0
    [627]     integral        8     'h8c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1935500000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5027
  dmac        integral        48    'h141e4ea5b15f
  smac        integral        48    'hbe71c4a7f69f
  ether_type  integral        16    'h1086
  pload       da(integral)    628   -
    [0]       integral        8     'h1b
    [1]       integral        8     'h67
    [2]       integral        8     'hfd
    [3]       integral        8     'h35
    [4]       integral        8     'h71
    ...       ...             ...   ...
    [623]     integral        8     'hcb
    [624]     integral        8     'h55
    [625]     integral        8     'h49
    [626]     integral        8     'hf0
    [627]     integral        8     'h8c
  crc         integral        32    'h0
--------------------------------------------------
TEST CASE PASSED

```
