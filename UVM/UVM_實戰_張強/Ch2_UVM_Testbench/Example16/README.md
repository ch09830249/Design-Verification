# xrun.log
1. case0_sequence
確實為 my_case0 的 base test 和 sequence 啟動
<img width="920" height="268" alt="image" src="https://github.com/user-attachments/assets/22f1123c-978a-4b8b-98a3-48d5d3d30aae" />

```
UVM_INFO my_case0.sv(29) @ 0: uvm_test_top [my_case0] my_case0 is new
UVM_INFO @ 0: reporter [RNTST] Running test my_case0...
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
UVM_INFO my_case0.sv(10) @ 0: uvm_test_top.env.i_agt.sqr@@case0_sequence [my_case0] my_case0's my_sequence
UVM_INFO my_driver.sv(43) @ 1100000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5005
  dmac                         integral        48    'haa0a1037880a
  smac                         integral        48    'h378cdffd98d2
  ether_type                   integral        16    'h5fa5
  pload                        da(integral)    1349  -
    [0]                        integral        8     'h6b
    [1]                        integral        8     'h4b
    [2]                        integral        8     'hc4
    [3]                        integral        8     'hc
    [4]                        integral        8     'h85
    ...                        ...             ...   ...
    [1344]                     integral        8     'heb
    [1345]                     integral        8     'h4b
    [1346]                     integral        8     'h19
    [1347]                     integral        8     'ha6
    [1348]                     integral        8     'hac
  crc                          integral        32    'h0
  begin_time                   time            64    1100000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 2500000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 2700000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 275700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 275700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5120
  dmac                         integral        48    'h20877eab09eb
  smac                         integral        48    'h5f5310949889
  ether_type                   integral        16    'h10c1
  pload                        da(integral)    552   -
    [0]                        integral        8     'hf0
    [1]                        integral        8     'h9d
    [2]                        integral        8     'h4e
    [3]                        integral        8     'h5d
    [4]                        integral        8     'h42
    ...                        ...             ...   ...
    [547]                      integral        8     'he8
    [548]                      integral        8     'h13
    [549]                      integral        8     'hec
    [550]                      integral        8     'h4b
    [551]                      integral        8     'hc5
  crc                          integral        32    'h0
  begin_time                   time            64    275700000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 275900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4994
  dmac        integral        48    'haa0a1037880a
  smac        integral        48    'h378cdffd98d2
  ether_type  integral        16    'h5fa5
  pload       da(integral)    1349  -
    [0]       integral        8     'h6b
    [1]       integral        8     'h4b
    [2]       integral        8     'hc4
    [3]       integral        8     'hc
    [4]       integral        8     'h85
    ...       ...             ...   ...
    [1344]    integral        8     'heb
    [1345]    integral        8     'h4b
    [1346]    integral        8     'h19
    [1347]    integral        8     'ha6
    [1348]    integral        8     'hac
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 275900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5074
  dmac        integral        48    'haa0a1037880a
  smac        integral        48    'h378cdffd98d2
  ether_type  integral        16    'h5fa5
  pload       da(integral)    1349  -
    [0]       integral        8     'h6b
    [1]       integral        8     'h4b
    [2]       integral        8     'hc4
    [3]       integral        8     'hc
    [4]       integral        8     'h85
    ...       ...             ...   ...
    [1344]    integral        8     'heb
    [1345]    integral        8     'h4b
    [1346]    integral        8     'h19
    [1347]    integral        8     'ha6
    [1348]    integral        8     'hac
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 276100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4961
  dmac        integral        48    'haa0a1037880a
  smac        integral        48    'h378cdffd98d2
  ether_type  integral        16    'h5fa5
  pload       da(integral)    1349  -
    [0]       integral        8     'h6b
    [1]       integral        8     'h4b
    [2]       integral        8     'hc4
    [3]       integral        8     'hc
    [4]       integral        8     'h85
    ...       ...             ...   ...
    [1344]    integral        8     'heb
    [1345]    integral        8     'h4b
    [1346]    integral        8     'h19
    [1347]    integral        8     'ha6
    [1348]    integral        8     'hac
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 276100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4961
  dmac        integral        48    'haa0a1037880a
  smac        integral        48    'h378cdffd98d2
  ether_type  integral        16    'h5fa5
  pload       da(integral)    1349  -
    [0]       integral        8     'h6b
    [1]       integral        8     'h4b
    [2]       integral        8     'hc4
    [3]       integral        8     'hc
    [4]       integral        8     'h85
    ...       ...             ...   ...
    [1344]    integral        8     'heb
    [1345]    integral        8     'h4b
    [1346]    integral        8     'h19
    [1347]    integral        8     'ha6
    [1348]    integral        8     'hac
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 277100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 277300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 390900000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 390900000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5135
  dmac                         integral        48    'ha173131769f0
  smac                         integral        48    'hf4955e5fedf2
  ether_type                   integral        16    'h6542
  pload                        da(integral)    1178  -
    [0]                        integral        8     'hba
    [1]                        integral        8     'hc2
    [2]                        integral        8     'h82
    [3]                        integral        8     'h9d
    [4]                        integral        8     'hfa
    ...                        ...             ...   ...
    [1173]                     integral        8     'h8a
    [1174]                     integral        8     'hd6
    [1175]                     integral        8     'h56
    [1176]                     integral        8     'hf9
    [1177]                     integral        8     'hfc
  crc                          integral        32    'h0
  begin_time                   time            64    390900000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 391100000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4986
  dmac        integral        48    'h20877eab09eb
  smac        integral        48    'h5f5310949889
  ether_type  integral        16    'h10c1
  pload       da(integral)    552   -
    [0]       integral        8     'hf0
    [1]       integral        8     'h9d
    [2]       integral        8     'h4e
    [3]       integral        8     'h5d
    [4]       integral        8     'h42
    ...       ...             ...   ...
    [547]     integral        8     'he8
    [548]     integral        8     'h13
    [549]     integral        8     'hec
    [550]     integral        8     'h4b
    [551]     integral        8     'hc5
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 391100000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4993
  dmac        integral        48    'h20877eab09eb
  smac        integral        48    'h5f5310949889
  ether_type  integral        16    'h10c1
  pload       da(integral)    552   -
    [0]       integral        8     'hf0
    [1]       integral        8     'h9d
    [2]       integral        8     'h4e
    [3]       integral        8     'h5d
    [4]       integral        8     'h42
    ...       ...             ...   ...
    [547]     integral        8     'he8
    [548]     integral        8     'h13
    [549]     integral        8     'hec
    [550]     integral        8     'h4b
    [551]     integral        8     'hc5
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 391300000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4970
  dmac        integral        48    'h20877eab09eb
  smac        integral        48    'h5f5310949889
  ether_type  integral        16    'h10c1
  pload       da(integral)    552   -
    [0]       integral        8     'hf0
    [1]       integral        8     'h9d
    [2]       integral        8     'h4e
    [3]       integral        8     'h5d
    [4]       integral        8     'h42
    ...       ...             ...   ...
    [547]     integral        8     'he8
    [548]     integral        8     'h13
    [549]     integral        8     'hec
    [550]     integral        8     'h4b
    [551]     integral        8     'hc5
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 391300000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4970
  dmac        integral        48    'h20877eab09eb
  smac        integral        48    'h5f5310949889
  ether_type  integral        16    'h10c1
  pload       da(integral)    552   -
    [0]       integral        8     'hf0
    [1]       integral        8     'h9d
    [2]       integral        8     'h4e
    [3]       integral        8     'h5d
    [4]       integral        8     'h42
    ...       ...             ...   ...
    [547]     integral        8     'he8
    [548]     integral        8     'h13
    [549]     integral        8     'hec
    [550]     integral        8     'h4b
    [551]     integral        8     'hc5
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 392300000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 392500000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 631300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 631300000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'h5d8a77cd09a0
  smac                         integral        48    'h86d7d1009b1f
  ether_type                   integral        16    'he848
  pload                        da(integral)    283   -
    [0]                        integral        8     'he5
    [1]                        integral        8     'hbe
    [2]                        integral        8     'hd0
    [3]                        integral        8     'ha
    [4]                        integral        8     'hd5
    ...                        ...             ...   ...
    [278]                      integral        8     'he5
    [279]                      integral        8     'h9d
    [280]                      integral        8     'h6a
    [281]                      integral        8     'hd4
    [282]                      integral        8     'hcd
  crc                          integral        32    'h0
  begin_time                   time            64    631300000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 631500000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5101
  dmac        integral        48    'ha173131769f0
  smac        integral        48    'hf4955e5fedf2
  ether_type  integral        16    'h6542
  pload       da(integral)    1178  -
    [0]       integral        8     'hba
    [1]       integral        8     'hc2
    [2]       integral        8     'h82
    [3]       integral        8     'h9d
    [4]       integral        8     'hfa
    ...       ...             ...   ...
    [1173]    integral        8     'h8a
    [1174]    integral        8     'hd6
    [1175]    integral        8     'h56
    [1176]    integral        8     'hf9
    [1177]    integral        8     'hfc
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 631500000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4995
  dmac        integral        48    'ha173131769f0
  smac        integral        48    'hf4955e5fedf2
  ether_type  integral        16    'h6542
  pload       da(integral)    1178  -
    [0]       integral        8     'hba
    [1]       integral        8     'hc2
    [2]       integral        8     'h82
    [3]       integral        8     'h9d
    [4]       integral        8     'hfa
    ...       ...             ...   ...
    [1173]    integral        8     'h8a
    [1174]    integral        8     'hd6
    [1175]    integral        8     'h56
    [1176]    integral        8     'hf9
    [1177]    integral        8     'hfc
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 631700000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'ha173131769f0
  smac        integral        48    'hf4955e5fedf2
  ether_type  integral        16    'h6542
  pload       da(integral)    1178  -
    [0]       integral        8     'hba
    [1]       integral        8     'hc2
    [2]       integral        8     'h82
    [3]       integral        8     'h9d
    [4]       integral        8     'hfa
    ...       ...             ...   ...
    [1173]    integral        8     'h8a
    [1174]    integral        8     'hd6
    [1175]    integral        8     'h56
    [1176]    integral        8     'hf9
    [1177]    integral        8     'hfc
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 631700000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'ha173131769f0
  smac        integral        48    'hf4955e5fedf2
  ether_type  integral        16    'h6542
  pload       da(integral)    1178  -
    [0]       integral        8     'hba
    [1]       integral        8     'hc2
    [2]       integral        8     'h82
    [3]       integral        8     'h9d
    [4]       integral        8     'hfa
    ...       ...             ...   ...
    [1173]    integral        8     'h8a
    [1174]    integral        8     'hd6
    [1175]    integral        8     'h56
    [1176]    integral        8     'hf9
    [1177]    integral        8     'hfc
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 632700000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 632900000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 692700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 692700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5058
  dmac                         integral        48    'hc2c8a6a2199d
  smac                         integral        48    'ha817ce7ab540
  ether_type                   integral        16    'h4da8
  pload                        da(integral)    1294  -
    [0]                        integral        8     'h43
    [1]                        integral        8     'he4
    [2]                        integral        8     'h24
    [3]                        integral        8     'h4f
    [4]                        integral        8     'h5e
    ...                        ...             ...   ...
    [1289]                     integral        8     'h81
    [1290]                     integral        8     'h71
    [1291]                     integral        8     'hda
    [1292]                     integral        8     'h9
    [1293]                     integral        8     'he9
  crc                          integral        32    'h0
  begin_time                   time            64    692700000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 692900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5051
  dmac        integral        48    'h5d8a77cd09a0
  smac        integral        48    'h86d7d1009b1f
  ether_type  integral        16    'he848
  pload       da(integral)    283   -
    [0]       integral        8     'he5
    [1]       integral        8     'hbe
    [2]       integral        8     'hd0
    [3]       integral        8     'ha
    [4]       integral        8     'hd5
    ...       ...             ...   ...
    [278]     integral        8     'he5
    [279]     integral        8     'h9d
    [280]     integral        8     'h6a
    [281]     integral        8     'hd4
    [282]     integral        8     'hcd
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 692900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5075
  dmac        integral        48    'h5d8a77cd09a0
  smac        integral        48    'h86d7d1009b1f
  ether_type  integral        16    'he848
  pload       da(integral)    283   -
    [0]       integral        8     'he5
    [1]       integral        8     'hbe
    [2]       integral        8     'hd0
    [3]       integral        8     'ha
    [4]       integral        8     'hd5
    ...       ...             ...   ...
    [278]     integral        8     'he5
    [279]     integral        8     'h9d
    [280]     integral        8     'h6a
    [281]     integral        8     'hd4
    [282]     integral        8     'hcd
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 693100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5138
  dmac        integral        48    'h5d8a77cd09a0
  smac        integral        48    'h86d7d1009b1f
  ether_type  integral        16    'he848
  pload       da(integral)    283   -
    [0]       integral        8     'he5
    [1]       integral        8     'hbe
    [2]       integral        8     'hd0
    [3]       integral        8     'ha
    [4]       integral        8     'hd5
    ...       ...             ...   ...
    [278]     integral        8     'he5
    [279]     integral        8     'h9d
    [280]     integral        8     'h6a
    [281]     integral        8     'hd4
    [282]     integral        8     'hcd
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 693100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5138
  dmac        integral        48    'h5d8a77cd09a0
  smac        integral        48    'h86d7d1009b1f
  ether_type  integral        16    'he848
  pload       da(integral)    283   -
    [0]       integral        8     'he5
    [1]       integral        8     'hbe
    [2]       integral        8     'hd0
    [3]       integral        8     'ha
    [4]       integral        8     'hd5
    ...       ...             ...   ...
    [278]     integral        8     'he5
    [279]     integral        8     'h9d
    [280]     integral        8     'h6a
    [281]     integral        8     'hd4
    [282]     integral        8     'hcd
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 694100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 694300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 956300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 956300000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5150
  dmac                         integral        48    'h244e7fe9e4ed
  smac                         integral        48    'h158cebfd972e
  ether_type                   integral        16    'heaeb
  pload                        da(integral)    1222  -
    [0]                        integral        8     'h79
    [1]                        integral        8     'hac
    [2]                        integral        8     'hf0
    [3]                        integral        8     'h2a
    [4]                        integral        8     'hbb
    ...                        ...             ...   ...
    [1217]                     integral        8     'h2f
    [1218]                     integral        8     'h6
    [1219]                     integral        8     'h3e
    [1220]                     integral        8     'h47
    [1221]                     integral        8     'hd4
  crc                          integral        32    'h0
  begin_time                   time            64    956300000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 956500000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5047
  dmac        integral        48    'hc2c8a6a2199d
  smac        integral        48    'ha817ce7ab540
  ether_type  integral        16    'h4da8
  pload       da(integral)    1294  -
    [0]       integral        8     'h43
    [1]       integral        8     'he4
    [2]       integral        8     'h24
    [3]       integral        8     'h4f
    [4]       integral        8     'h5e
    ...       ...             ...   ...
    [1289]    integral        8     'h81
    [1290]    integral        8     'h71
    [1291]    integral        8     'hda
    [1292]    integral        8     'h9
    [1293]    integral        8     'he9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 956500000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5032
  dmac        integral        48    'hc2c8a6a2199d
  smac        integral        48    'ha817ce7ab540
  ether_type  integral        16    'h4da8
  pload       da(integral)    1294  -
    [0]       integral        8     'h43
    [1]       integral        8     'he4
    [2]       integral        8     'h24
    [3]       integral        8     'h4f
    [4]       integral        8     'h5e
    ...       ...             ...   ...
    [1289]    integral        8     'h81
    [1290]    integral        8     'h71
    [1291]    integral        8     'hda
    [1292]    integral        8     'h9
    [1293]    integral        8     'he9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 956700000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5149
  dmac        integral        48    'hc2c8a6a2199d
  smac        integral        48    'ha817ce7ab540
  ether_type  integral        16    'h4da8
  pload       da(integral)    1294  -
    [0]       integral        8     'h43
    [1]       integral        8     'he4
    [2]       integral        8     'h24
    [3]       integral        8     'h4f
    [4]       integral        8     'h5e
    ...       ...             ...   ...
    [1289]    integral        8     'h81
    [1290]    integral        8     'h71
    [1291]    integral        8     'hda
    [1292]    integral        8     'h9
    [1293]    integral        8     'he9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 956700000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5149
  dmac        integral        48    'hc2c8a6a2199d
  smac        integral        48    'ha817ce7ab540
  ether_type  integral        16    'h4da8
  pload       da(integral)    1294  -
    [0]       integral        8     'h43
    [1]       integral        8     'he4
    [2]       integral        8     'h24
    [3]       integral        8     'h4f
    [4]       integral        8     'h5e
    ...       ...             ...   ...
    [1289]    integral        8     'h81
    [1290]    integral        8     'h71
    [1291]    integral        8     'hda
    [1292]    integral        8     'h9
    [1293]    integral        8     'he9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 957700000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 957900000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1205500000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 1205500000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5112
  dmac                         integral        48    'h6aa38609024
  smac                         integral        48    'ha7e9a22dab45
  ether_type                   integral        16    'h92e2
  pload                        da(integral)    1330  -
    [0]                        integral        8     'hf4
    [1]                        integral        8     'h83
    [2]                        integral        8     'hc7
    [3]                        integral        8     'ha6
    [4]                        integral        8     'hbf
    ...                        ...             ...   ...
    [1325]                     integral        8     'h2b
    [1326]                     integral        8     'h68
    [1327]                     integral        8     'h3c
    [1328]                     integral        8     'hb
    [1329]                     integral        8     'h9d
  crc                          integral        32    'h0
  begin_time                   time            64    1205500000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1205700000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5028
  dmac        integral        48    'h244e7fe9e4ed
  smac        integral        48    'h158cebfd972e
  ether_type  integral        16    'heaeb
  pload       da(integral)    1222  -
    [0]       integral        8     'h79
    [1]       integral        8     'hac
    [2]       integral        8     'hf0
    [3]       integral        8     'h2a
    [4]       integral        8     'hbb
    ...       ...             ...   ...
    [1217]    integral        8     'h2f
    [1218]    integral        8     'h6
    [1219]    integral        8     'h3e
    [1220]    integral        8     'h47
    [1221]    integral        8     'hd4
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1205700000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5083
  dmac        integral        48    'h244e7fe9e4ed
  smac        integral        48    'h158cebfd972e
  ether_type  integral        16    'heaeb
  pload       da(integral)    1222  -
    [0]       integral        8     'h79
    [1]       integral        8     'hac
    [2]       integral        8     'hf0
    [3]       integral        8     'h2a
    [4]       integral        8     'hbb
    ...       ...             ...   ...
    [1217]    integral        8     'h2f
    [1218]    integral        8     'h6
    [1219]    integral        8     'h3e
    [1220]    integral        8     'h47
    [1221]    integral        8     'hd4
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1205900000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5113
  dmac        integral        48    'h244e7fe9e4ed
  smac        integral        48    'h158cebfd972e
  ether_type  integral        16    'heaeb
  pload       da(integral)    1222  -
    [0]       integral        8     'h79
    [1]       integral        8     'hac
    [2]       integral        8     'hf0
    [3]       integral        8     'h2a
    [4]       integral        8     'hbb
    ...       ...             ...   ...
    [1217]    integral        8     'h2f
    [1218]    integral        8     'h6
    [1219]    integral        8     'h3e
    [1220]    integral        8     'h47
    [1221]    integral        8     'hd4
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1205900000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5113
  dmac        integral        48    'h244e7fe9e4ed
  smac        integral        48    'h158cebfd972e
  ether_type  integral        16    'heaeb
  pload       da(integral)    1222  -
    [0]       integral        8     'h79
    [1]       integral        8     'hac
    [2]       integral        8     'hf0
    [3]       integral        8     'h2a
    [4]       integral        8     'hbb
    ...       ...             ...   ...
    [1217]    integral        8     'h2f
    [1218]    integral        8     'h6
    [1219]    integral        8     'h3e
    [1220]    integral        8     'h47
    [1221]    integral        8     'hd4
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1206900000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1207100000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1476300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 1476300000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5158
  dmac                         integral        48    'h7288b1173f4d
  smac                         integral        48    'he948e23d58d4
  ether_type                   integral        16    'h224
  pload                        da(integral)    1365  -
    [0]                        integral        8     'h69
    [1]                        integral        8     'h26
    [2]                        integral        8     'h4b
    [3]                        integral        8     'hd6
    [4]                        integral        8     'he0
    ...                        ...             ...   ...
    [1360]                     integral        8     'hc6
    [1361]                     integral        8     'ha9
    [1362]                     integral        8     'hb8
    [1363]                     integral        8     'hbd
    [1364]                     integral        8     'h1d
  crc                          integral        32    'h0
  begin_time                   time            64    1476300000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1476500000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5044
  dmac        integral        48    'h6aa38609024
  smac        integral        48    'ha7e9a22dab45
  ether_type  integral        16    'h92e2
  pload       da(integral)    1330  -
    [0]       integral        8     'hf4
    [1]       integral        8     'h83
    [2]       integral        8     'hc7
    [3]       integral        8     'ha6
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [1325]    integral        8     'h2b
    [1326]    integral        8     'h68
    [1327]    integral        8     'h3c
    [1328]    integral        8     'hb
    [1329]    integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1476500000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5036
  dmac        integral        48    'h6aa38609024
  smac        integral        48    'ha7e9a22dab45
  ether_type  integral        16    'h92e2
  pload       da(integral)    1330  -
    [0]       integral        8     'hf4
    [1]       integral        8     'h83
    [2]       integral        8     'hc7
    [3]       integral        8     'ha6
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [1325]    integral        8     'h2b
    [1326]    integral        8     'h68
    [1327]    integral        8     'h3c
    [1328]    integral        8     'hb
    [1329]    integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1476700000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5155
  dmac        integral        48    'h6aa38609024
  smac        integral        48    'ha7e9a22dab45
  ether_type  integral        16    'h92e2
  pload       da(integral)    1330  -
    [0]       integral        8     'hf4
    [1]       integral        8     'h83
    [2]       integral        8     'hc7
    [3]       integral        8     'ha6
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [1325]    integral        8     'h2b
    [1326]    integral        8     'h68
    [1327]    integral        8     'h3c
    [1328]    integral        8     'hb
    [1329]    integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1476700000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5155
  dmac        integral        48    'h6aa38609024
  smac        integral        48    'ha7e9a22dab45
  ether_type  integral        16    'h92e2
  pload       da(integral)    1330  -
    [0]       integral        8     'hf4
    [1]       integral        8     'h83
    [2]       integral        8     'hc7
    [3]       integral        8     'ha6
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [1325]    integral        8     'h2b
    [1326]    integral        8     'h68
    [1327]    integral        8     'h3c
    [1328]    integral        8     'hb
    [1329]    integral        8     'h9d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1477700000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1477900000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1754100000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 1754100000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5119
  dmac                         integral        48    'h359534f35019
  smac                         integral        48    'hed6962cc8381
  ether_type                   integral        16    'hc443
  pload                        da(integral)    43    -
    [0]                        integral        8     'h56
    [1]                        integral        8     'h99
    [2]                        integral        8     'had
    [3]                        integral        8     'h87
    [4]                        integral        8     'hc1
    ...                        ...             ...   ...
    [38]                       integral        8     'h10
    [39]                       integral        8     'hbe
    [40]                       integral        8     'h10
    [41]                       integral        8     'ha7
    [42]                       integral        8     'h52
  crc                          integral        32    'h0
  begin_time                   time            64    1754100000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1754300000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5057
  dmac        integral        48    'h7288b1173f4d
  smac        integral        48    'he948e23d58d4
  ether_type  integral        16    'h224
  pload       da(integral)    1365  -
    [0]       integral        8     'h69
    [1]       integral        8     'h26
    [2]       integral        8     'h4b
    [3]       integral        8     'hd6
    [4]       integral        8     'he0
    ...       ...             ...   ...
    [1360]    integral        8     'hc6
    [1361]    integral        8     'ha9
    [1362]    integral        8     'hb8
    [1363]    integral        8     'hbd
    [1364]    integral        8     'h1d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1754300000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5063
  dmac        integral        48    'h7288b1173f4d
  smac        integral        48    'he948e23d58d4
  ether_type  integral        16    'h224
  pload       da(integral)    1365  -
    [0]       integral        8     'h69
    [1]       integral        8     'h26
    [2]       integral        8     'h4b
    [3]       integral        8     'hd6
    [4]       integral        8     'he0
    ...       ...             ...   ...
    [1360]    integral        8     'hc6
    [1361]    integral        8     'ha9
    [1362]    integral        8     'hb8
    [1363]    integral        8     'hbd
    [1364]    integral        8     'h1d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1754500000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5115
  dmac        integral        48    'h7288b1173f4d
  smac        integral        48    'he948e23d58d4
  ether_type  integral        16    'h224
  pload       da(integral)    1365  -
    [0]       integral        8     'h69
    [1]       integral        8     'h26
    [2]       integral        8     'h4b
    [3]       integral        8     'hd6
    [4]       integral        8     'he0
    ...       ...             ...   ...
    [1360]    integral        8     'hc6
    [1361]    integral        8     'ha9
    [1362]    integral        8     'hb8
    [1363]    integral        8     'hbd
    [1364]    integral        8     'h1d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1754500000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5115
  dmac        integral        48    'h7288b1173f4d
  smac        integral        48    'he948e23d58d4
  ether_type  integral        16    'h224
  pload       da(integral)    1365  -
    [0]       integral        8     'h69
    [1]       integral        8     'h26
    [2]       integral        8     'h4b
    [3]       integral        8     'hd6
    [4]       integral        8     'he0
    ...       ...             ...   ...
    [1360]    integral        8     'hc6
    [1361]    integral        8     'ha9
    [1362]    integral        8     'hb8
    [1363]    integral        8     'hbd
    [1364]    integral        8     'h1d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1755500000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1755700000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1767500000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 1767500000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5137
  dmac                         integral        48    'h4555b9e86f05
  smac                         integral        48    'he1c946813019
  ether_type                   integral        16    'hd3cc
  pload                        da(integral)    695   -
    [0]                        integral        8     'h7f
    [1]                        integral        8     'h9d
    [2]                        integral        8     'h9f
    [3]                        integral        8     'hf6
    [4]                        integral        8     'h93
    ...                        ...             ...   ...
    [690]                      integral        8     'h4
    [691]                      integral        8     'h2e
    [692]                      integral        8     'hcb
    [693]                      integral        8     'h47
    [694]                      integral        8     'h14
  crc                          integral        32    'h0
  begin_time                   time            64    1767500000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case0_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case0_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1767700000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5146
  dmac        integral        48    'h359534f35019
  smac        integral        48    'hed6962cc8381
  ether_type  integral        16    'hc443
  pload       da(integral)    43    -
    [0]       integral        8     'h56
    [1]       integral        8     'h99
    [2]       integral        8     'had
    [3]       integral        8     'h87
    [4]       integral        8     'hc1
    ...       ...             ...   ...
    [38]      integral        8     'h10
    [39]      integral        8     'hbe
    [40]      integral        8     'h10
    [41]      integral        8     'ha7
    [42]      integral        8     'h52
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1767700000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5078
  dmac        integral        48    'h359534f35019
  smac        integral        48    'hed6962cc8381
  ether_type  integral        16    'hc443
  pload       da(integral)    43    -
    [0]       integral        8     'h56
    [1]       integral        8     'h99
    [2]       integral        8     'had
    [3]       integral        8     'h87
    [4]       integral        8     'hc1
    ...       ...             ...   ...
    [38]      integral        8     'h10
    [39]      integral        8     'hbe
    [40]      integral        8     'h10
    [41]      integral        8     'ha7
    [42]      integral        8     'h52
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1767900000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5027
  dmac        integral        48    'h359534f35019
  smac        integral        48    'hed6962cc8381
  ether_type  integral        16    'hc443
  pload       da(integral)    43    -
    [0]       integral        8     'h56
    [1]       integral        8     'h99
    [2]       integral        8     'had
    [3]       integral        8     'h87
    [4]       integral        8     'hc1
    ...       ...             ...   ...
    [38]      integral        8     'h10
    [39]      integral        8     'hbe
    [40]      integral        8     'h10
    [41]      integral        8     'ha7
    [42]      integral        8     'h52
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1767900000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5027
  dmac        integral        48    'h359534f35019
  smac        integral        48    'hed6962cc8381
  ether_type  integral        16    'hc443
  pload       da(integral)    43    -
    [0]       integral        8     'h56
    [1]       integral        8     'h99
    [2]       integral        8     'had
    [3]       integral        8     'h87
    [4]       integral        8     'hc1
    ...       ...             ...   ...
    [38]      integral        8     'h10
    [39]      integral        8     'hbe
    [40]      integral        8     'h10
    [41]      integral        8     'ha7
    [42]      integral        8     'h52
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1768900000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1769100000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1911300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
TEST CASE PASSED
```
2. case1_sequence
確實為 my_case1 的 base test 和 sequence 啟動
<img width="917" height="277" alt="image" src="https://github.com/user-attachments/assets/fd8e25b2-f94e-476a-961b-414fee8d4658" />

且 payload size 也確實是 60
<img width="838" height="452" alt="image" src="https://github.com/user-attachments/assets/08cece66-80d8-42bc-b4e9-e7c0cb0f1ead" />

```
UVM_INFO my_case1.sv(28) @ 0: uvm_test_top [my_case1] my_case1 is new
UVM_INFO @ 0: reporter [RNTST] Running test my_case1...
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
UVM_INFO my_case1.sv(9) @ 0: uvm_test_top.env.i_agt.sqr@@case1_sequence [my_case1] my_case1's my_sequence
UVM_INFO my_driver.sv(43) @ 1100000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5005
  dmac                         integral        48    'h544e7692e0cb
  smac                         integral        48    'h67663c81d601
  ether_type                   integral        16    'h568f
  pload                        da(integral)    60    -
    [0]                        integral        8     'hea
    [1]                        integral        8     'hef
    [2]                        integral        8     'h16
    [3]                        integral        8     'hab
    [4]                        integral        8     'h1f
    ...                        ...             ...   ...
    [55]                       integral        8     'h1e
    [56]                       integral        8     'h84
    [57]                       integral        8     'h62
    [58]                       integral        8     'h6b
    [59]                       integral        8     'h0
  crc                          integral        32    'h0
  begin_time                   time            64    1100000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 2500000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 2700000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 17900000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 17900000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5120
  dmac                         integral        48    'hd62f302ca5ae
  smac                         integral        48    'h671d44864c7d
  ether_type                   integral        16    'h7e56
  pload                        da(integral)    60    -
    [0]                        integral        8     'h6
    [1]                        integral        8     'h74
    [2]                        integral        8     'h68
    [3]                        integral        8     'h35
    [4]                        integral        8     'h6f
    ...                        ...             ...   ...
    [55]                       integral        8     'ha3
    [56]                       integral        8     'h24
    [57]                       integral        8     'h62
    [58]                       integral        8     'hfc
    [59]                       integral        8     'h82
  crc                          integral        32    'h0
  begin_time                   time            64    17900000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 18100000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4994
  dmac        integral        48    'h544e7692e0cb
  smac        integral        48    'h67663c81d601
  ether_type  integral        16    'h568f
  pload       da(integral)    60    -
    [0]       integral        8     'hea
    [1]       integral        8     'hef
    [2]       integral        8     'h16
    [3]       integral        8     'hab
    [4]       integral        8     'h1f
    ...       ...             ...   ...
    [55]      integral        8     'h1e
    [56]      integral        8     'h84
    [57]      integral        8     'h62
    [58]      integral        8     'h6b
    [59]      integral        8     'h0
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 18100000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5074
  dmac        integral        48    'h544e7692e0cb
  smac        integral        48    'h67663c81d601
  ether_type  integral        16    'h568f
  pload       da(integral)    60    -
    [0]       integral        8     'hea
    [1]       integral        8     'hef
    [2]       integral        8     'h16
    [3]       integral        8     'hab
    [4]       integral        8     'h1f
    ...       ...             ...   ...
    [55]      integral        8     'h1e
    [56]      integral        8     'h84
    [57]      integral        8     'h62
    [58]      integral        8     'h6b
    [59]      integral        8     'h0
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 18300000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4961
  dmac        integral        48    'h544e7692e0cb
  smac        integral        48    'h67663c81d601
  ether_type  integral        16    'h568f
  pload       da(integral)    60    -
    [0]       integral        8     'hea
    [1]       integral        8     'hef
    [2]       integral        8     'h16
    [3]       integral        8     'hab
    [4]       integral        8     'h1f
    ...       ...             ...   ...
    [55]      integral        8     'h1e
    [56]      integral        8     'h84
    [57]      integral        8     'h62
    [58]      integral        8     'h6b
    [59]      integral        8     'h0
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 18300000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4961
  dmac        integral        48    'h544e7692e0cb
  smac        integral        48    'h67663c81d601
  ether_type  integral        16    'h568f
  pload       da(integral)    60    -
    [0]       integral        8     'hea
    [1]       integral        8     'hef
    [2]       integral        8     'h16
    [3]       integral        8     'hab
    [4]       integral        8     'h1f
    ...       ...             ...   ...
    [55]      integral        8     'h1e
    [56]      integral        8     'h84
    [57]      integral        8     'h62
    [58]      integral        8     'h6b
    [59]      integral        8     'h0
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 19300000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 19500000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 34700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 34700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5135
  dmac                         integral        48    'hacf74b0e3b46
  smac                         integral        48    'hd97e7bab2e88
  ether_type                   integral        16    'h47d9
  pload                        da(integral)    60    -
    [0]                        integral        8     'hb3
    [1]                        integral        8     'h76
    [2]                        integral        8     'h4a
    [3]                        integral        8     'h8
    [4]                        integral        8     'h25
    ...                        ...             ...   ...
    [55]                       integral        8     'h59
    [56]                       integral        8     'h6a
    [57]                       integral        8     'h6f
    [58]                       integral        8     'hbc
    [59]                       integral        8     'hf9
  crc                          integral        32    'h0
  begin_time                   time            64    34700000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 34900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4986
  dmac        integral        48    'hd62f302ca5ae
  smac        integral        48    'h671d44864c7d
  ether_type  integral        16    'h7e56
  pload       da(integral)    60    -
    [0]       integral        8     'h6
    [1]       integral        8     'h74
    [2]       integral        8     'h68
    [3]       integral        8     'h35
    [4]       integral        8     'h6f
    ...       ...             ...   ...
    [55]      integral        8     'ha3
    [56]      integral        8     'h24
    [57]      integral        8     'h62
    [58]      integral        8     'hfc
    [59]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 34900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4993
  dmac        integral        48    'hd62f302ca5ae
  smac        integral        48    'h671d44864c7d
  ether_type  integral        16    'h7e56
  pload       da(integral)    60    -
    [0]       integral        8     'h6
    [1]       integral        8     'h74
    [2]       integral        8     'h68
    [3]       integral        8     'h35
    [4]       integral        8     'h6f
    ...       ...             ...   ...
    [55]      integral        8     'ha3
    [56]      integral        8     'h24
    [57]      integral        8     'h62
    [58]      integral        8     'hfc
    [59]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 35100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4970
  dmac        integral        48    'hd62f302ca5ae
  smac        integral        48    'h671d44864c7d
  ether_type  integral        16    'h7e56
  pload       da(integral)    60    -
    [0]       integral        8     'h6
    [1]       integral        8     'h74
    [2]       integral        8     'h68
    [3]       integral        8     'h35
    [4]       integral        8     'h6f
    ...       ...             ...   ...
    [55]      integral        8     'ha3
    [56]      integral        8     'h24
    [57]      integral        8     'h62
    [58]      integral        8     'hfc
    [59]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 35100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4970
  dmac        integral        48    'hd62f302ca5ae
  smac        integral        48    'h671d44864c7d
  ether_type  integral        16    'h7e56
  pload       da(integral)    60    -
    [0]       integral        8     'h6
    [1]       integral        8     'h74
    [2]       integral        8     'h68
    [3]       integral        8     'h35
    [4]       integral        8     'h6f
    ...       ...             ...   ...
    [55]      integral        8     'ha3
    [56]      integral        8     'h24
    [57]      integral        8     'h62
    [58]      integral        8     'hfc
    [59]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 36100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 36300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 51500000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 51500000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5100
  dmac                         integral        48    'he478c737a192
  smac                         integral        48    'h55137990e380
  ether_type                   integral        16    'h7833
  pload                        da(integral)    60    -
    [0]                        integral        8     'h18
    [1]                        integral        8     'h45
    [2]                        integral        8     'hf5
    [3]                        integral        8     'hc6
    [4]                        integral        8     'haf
    ...                        ...             ...   ...
    [55]                       integral        8     'h4c
    [56]                       integral        8     'he4
    [57]                       integral        8     'h97
    [58]                       integral        8     'h3e
    [59]                       integral        8     'ha7
  crc                          integral        32    'h0
  begin_time                   time            64    51500000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 51700000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5101
  dmac        integral        48    'hacf74b0e3b46
  smac        integral        48    'hd97e7bab2e88
  ether_type  integral        16    'h47d9
  pload       da(integral)    60    -
    [0]       integral        8     'hb3
    [1]       integral        8     'h76
    [2]       integral        8     'h4a
    [3]       integral        8     'h8
    [4]       integral        8     'h25
    ...       ...             ...   ...
    [55]      integral        8     'h59
    [56]      integral        8     'h6a
    [57]      integral        8     'h6f
    [58]      integral        8     'hbc
    [59]      integral        8     'hf9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 51700000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4995
  dmac        integral        48    'hacf74b0e3b46
  smac        integral        48    'hd97e7bab2e88
  ether_type  integral        16    'h47d9
  pload       da(integral)    60    -
    [0]       integral        8     'hb3
    [1]       integral        8     'h76
    [2]       integral        8     'h4a
    [3]       integral        8     'h8
    [4]       integral        8     'h25
    ...       ...             ...   ...
    [55]      integral        8     'h59
    [56]      integral        8     'h6a
    [57]      integral        8     'h6f
    [58]      integral        8     'hbc
    [59]      integral        8     'hf9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 51900000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'hacf74b0e3b46
  smac        integral        48    'hd97e7bab2e88
  ether_type  integral        16    'h47d9
  pload       da(integral)    60    -
    [0]       integral        8     'hb3
    [1]       integral        8     'h76
    [2]       integral        8     'h4a
    [3]       integral        8     'h8
    [4]       integral        8     'h25
    ...       ...             ...   ...
    [55]      integral        8     'h59
    [56]      integral        8     'h6a
    [57]      integral        8     'h6f
    [58]      integral        8     'hbc
    [59]      integral        8     'hf9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 51900000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'hacf74b0e3b46
  smac        integral        48    'hd97e7bab2e88
  ether_type  integral        16    'h47d9
  pload       da(integral)    60    -
    [0]       integral        8     'hb3
    [1]       integral        8     'h76
    [2]       integral        8     'h4a
    [3]       integral        8     'h8
    [4]       integral        8     'h25
    ...       ...             ...   ...
    [55]      integral        8     'h59
    [56]      integral        8     'h6a
    [57]      integral        8     'h6f
    [58]      integral        8     'hbc
    [59]      integral        8     'hf9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 52900000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 53100000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 68300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 68300000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5058
  dmac                         integral        48    'hda0ea4a8d895
  smac                         integral        48    'hed4c75c68761
  ether_type                   integral        16    'h1fe
  pload                        da(integral)    60    -
    [0]                        integral        8     'hc7
    [1]                        integral        8     'h77
    [2]                        integral        8     'h73
    [3]                        integral        8     'h6a
    [4]                        integral        8     'hf2
    ...                        ...             ...   ...
    [55]                       integral        8     'h6f
    [56]                       integral        8     'h8b
    [57]                       integral        8     'h52
    [58]                       integral        8     'h24
    [59]                       integral        8     'hc8
  crc                          integral        32    'h0
  begin_time                   time            64    68300000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 68500000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5051
  dmac        integral        48    'he478c737a192
  smac        integral        48    'h55137990e380
  ether_type  integral        16    'h7833
  pload       da(integral)    60    -
    [0]       integral        8     'h18
    [1]       integral        8     'h45
    [2]       integral        8     'hf5
    [3]       integral        8     'hc6
    [4]       integral        8     'haf
    ...       ...             ...   ...
    [55]      integral        8     'h4c
    [56]      integral        8     'he4
    [57]      integral        8     'h97
    [58]      integral        8     'h3e
    [59]      integral        8     'ha7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 68500000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5075
  dmac        integral        48    'he478c737a192
  smac        integral        48    'h55137990e380
  ether_type  integral        16    'h7833
  pload       da(integral)    60    -
    [0]       integral        8     'h18
    [1]       integral        8     'h45
    [2]       integral        8     'hf5
    [3]       integral        8     'hc6
    [4]       integral        8     'haf
    ...       ...             ...   ...
    [55]      integral        8     'h4c
    [56]      integral        8     'he4
    [57]      integral        8     'h97
    [58]      integral        8     'h3e
    [59]      integral        8     'ha7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 68700000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5138
  dmac        integral        48    'he478c737a192
  smac        integral        48    'h55137990e380
  ether_type  integral        16    'h7833
  pload       da(integral)    60    -
    [0]       integral        8     'h18
    [1]       integral        8     'h45
    [2]       integral        8     'hf5
    [3]       integral        8     'hc6
    [4]       integral        8     'haf
    ...       ...             ...   ...
    [55]      integral        8     'h4c
    [56]      integral        8     'he4
    [57]      integral        8     'h97
    [58]      integral        8     'h3e
    [59]      integral        8     'ha7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 68700000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5138
  dmac        integral        48    'he478c737a192
  smac        integral        48    'h55137990e380
  ether_type  integral        16    'h7833
  pload       da(integral)    60    -
    [0]       integral        8     'h18
    [1]       integral        8     'h45
    [2]       integral        8     'hf5
    [3]       integral        8     'hc6
    [4]       integral        8     'haf
    ...       ...             ...   ...
    [55]      integral        8     'h4c
    [56]      integral        8     'he4
    [57]      integral        8     'h97
    [58]      integral        8     'h3e
    [59]      integral        8     'ha7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 69700000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 69900000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 85100000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 85100000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5150
  dmac                         integral        48    'h305ee361e04c
  smac                         integral        48    'h8eb838bcfe2e
  ether_type                   integral        16    'hf2a0
  pload                        da(integral)    60    -
    [0]                        integral        8     'h2c
    [1]                        integral        8     'h76
    [2]                        integral        8     'hbc
    [3]                        integral        8     'hf8
    [4]                        integral        8     'h9
    ...                        ...             ...   ...
    [55]                       integral        8     'hcd
    [56]                       integral        8     'h67
    [57]                       integral        8     'h29
    [58]                       integral        8     'hcc
    [59]                       integral        8     'h1f
  crc                          integral        32    'h0
  begin_time                   time            64    85100000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 85300000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5047
  dmac        integral        48    'hda0ea4a8d895
  smac        integral        48    'hed4c75c68761
  ether_type  integral        16    'h1fe
  pload       da(integral)    60    -
    [0]       integral        8     'hc7
    [1]       integral        8     'h77
    [2]       integral        8     'h73
    [3]       integral        8     'h6a
    [4]       integral        8     'hf2
    ...       ...             ...   ...
    [55]      integral        8     'h6f
    [56]      integral        8     'h8b
    [57]      integral        8     'h52
    [58]      integral        8     'h24
    [59]      integral        8     'hc8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 85300000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5032
  dmac        integral        48    'hda0ea4a8d895
  smac        integral        48    'hed4c75c68761
  ether_type  integral        16    'h1fe
  pload       da(integral)    60    -
    [0]       integral        8     'hc7
    [1]       integral        8     'h77
    [2]       integral        8     'h73
    [3]       integral        8     'h6a
    [4]       integral        8     'hf2
    ...       ...             ...   ...
    [55]      integral        8     'h6f
    [56]      integral        8     'h8b
    [57]      integral        8     'h52
    [58]      integral        8     'h24
    [59]      integral        8     'hc8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 85500000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5149
  dmac        integral        48    'hda0ea4a8d895
  smac        integral        48    'hed4c75c68761
  ether_type  integral        16    'h1fe
  pload       da(integral)    60    -
    [0]       integral        8     'hc7
    [1]       integral        8     'h77
    [2]       integral        8     'h73
    [3]       integral        8     'h6a
    [4]       integral        8     'hf2
    ...       ...             ...   ...
    [55]      integral        8     'h6f
    [56]      integral        8     'h8b
    [57]      integral        8     'h52
    [58]      integral        8     'h24
    [59]      integral        8     'hc8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 85500000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5149
  dmac        integral        48    'hda0ea4a8d895
  smac        integral        48    'hed4c75c68761
  ether_type  integral        16    'h1fe
  pload       da(integral)    60    -
    [0]       integral        8     'hc7
    [1]       integral        8     'h77
    [2]       integral        8     'h73
    [3]       integral        8     'h6a
    [4]       integral        8     'hf2
    ...       ...             ...   ...
    [55]      integral        8     'h6f
    [56]      integral        8     'h8b
    [57]      integral        8     'h52
    [58]      integral        8     'h24
    [59]      integral        8     'hc8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 86500000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 86700000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 101900000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 101900000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5112
  dmac                         integral        48    'h5c688362b8b8
  smac                         integral        48    'h79d9294432a0
  ether_type                   integral        16    'hc6ec
  pload                        da(integral)    60    -
    [0]                        integral        8     'h26
    [1]                        integral        8     'h78
    [2]                        integral        8     'h4e
    [3]                        integral        8     'hae
    [4]                        integral        8     'hb9
    ...                        ...             ...   ...
    [55]                       integral        8     'h6e
    [56]                       integral        8     'h8b
    [57]                       integral        8     'hb3
    [58]                       integral        8     'hfe
    [59]                       integral        8     'h6b
  crc                          integral        32    'h0
  begin_time                   time            64    101900000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 102100000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5028
  dmac        integral        48    'h305ee361e04c
  smac        integral        48    'h8eb838bcfe2e
  ether_type  integral        16    'hf2a0
  pload       da(integral)    60    -
    [0]       integral        8     'h2c
    [1]       integral        8     'h76
    [2]       integral        8     'hbc
    [3]       integral        8     'hf8
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [55]      integral        8     'hcd
    [56]      integral        8     'h67
    [57]      integral        8     'h29
    [58]      integral        8     'hcc
    [59]      integral        8     'h1f
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 102100000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5083
  dmac        integral        48    'h305ee361e04c
  smac        integral        48    'h8eb838bcfe2e
  ether_type  integral        16    'hf2a0
  pload       da(integral)    60    -
    [0]       integral        8     'h2c
    [1]       integral        8     'h76
    [2]       integral        8     'hbc
    [3]       integral        8     'hf8
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [55]      integral        8     'hcd
    [56]      integral        8     'h67
    [57]      integral        8     'h29
    [58]      integral        8     'hcc
    [59]      integral        8     'h1f
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 102300000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5113
  dmac        integral        48    'h305ee361e04c
  smac        integral        48    'h8eb838bcfe2e
  ether_type  integral        16    'hf2a0
  pload       da(integral)    60    -
    [0]       integral        8     'h2c
    [1]       integral        8     'h76
    [2]       integral        8     'hbc
    [3]       integral        8     'hf8
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [55]      integral        8     'hcd
    [56]      integral        8     'h67
    [57]      integral        8     'h29
    [58]      integral        8     'hcc
    [59]      integral        8     'h1f
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 102300000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5113
  dmac        integral        48    'h305ee361e04c
  smac        integral        48    'h8eb838bcfe2e
  ether_type  integral        16    'hf2a0
  pload       da(integral)    60    -
    [0]       integral        8     'h2c
    [1]       integral        8     'h76
    [2]       integral        8     'hbc
    [3]       integral        8     'hf8
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [55]      integral        8     'hcd
    [56]      integral        8     'h67
    [57]      integral        8     'h29
    [58]      integral        8     'hcc
    [59]      integral        8     'h1f
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 103300000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 103500000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 118700000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 118700000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5158
  dmac                         integral        48    'hd18584ab61da
  smac                         integral        48    'h411db14b6b43
  ether_type                   integral        16    'h77d7
  pload                        da(integral)    60    -
    [0]                        integral        8     'h8d
    [1]                        integral        8     'ha7
    [2]                        integral        8     'h34
    [3]                        integral        8     'hd
    [4]                        integral        8     'h5d
    ...                        ...             ...   ...
    [55]                       integral        8     'h38
    [56]                       integral        8     'hc9
    [57]                       integral        8     'h39
    [58]                       integral        8     'hcc
    [59]                       integral        8     'h6c
  crc                          integral        32    'h0
  begin_time                   time            64    118700000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 118900000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5044
  dmac        integral        48    'h5c688362b8b8
  smac        integral        48    'h79d9294432a0
  ether_type  integral        16    'hc6ec
  pload       da(integral)    60    -
    [0]       integral        8     'h26
    [1]       integral        8     'h78
    [2]       integral        8     'h4e
    [3]       integral        8     'hae
    [4]       integral        8     'hb9
    ...       ...             ...   ...
    [55]      integral        8     'h6e
    [56]      integral        8     'h8b
    [57]      integral        8     'hb3
    [58]      integral        8     'hfe
    [59]      integral        8     'h6b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 118900000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5036
  dmac        integral        48    'h5c688362b8b8
  smac        integral        48    'h79d9294432a0
  ether_type  integral        16    'hc6ec
  pload       da(integral)    60    -
    [0]       integral        8     'h26
    [1]       integral        8     'h78
    [2]       integral        8     'h4e
    [3]       integral        8     'hae
    [4]       integral        8     'hb9
    ...       ...             ...   ...
    [55]      integral        8     'h6e
    [56]      integral        8     'h8b
    [57]      integral        8     'hb3
    [58]      integral        8     'hfe
    [59]      integral        8     'h6b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 119100000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5155
  dmac        integral        48    'h5c688362b8b8
  smac        integral        48    'h79d9294432a0
  ether_type  integral        16    'hc6ec
  pload       da(integral)    60    -
    [0]       integral        8     'h26
    [1]       integral        8     'h78
    [2]       integral        8     'h4e
    [3]       integral        8     'hae
    [4]       integral        8     'hb9
    ...       ...             ...   ...
    [55]      integral        8     'h6e
    [56]      integral        8     'h8b
    [57]      integral        8     'hb3
    [58]      integral        8     'hfe
    [59]      integral        8     'h6b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 119100000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5155
  dmac        integral        48    'h5c688362b8b8
  smac        integral        48    'h79d9294432a0
  ether_type  integral        16    'hc6ec
  pload       da(integral)    60    -
    [0]       integral        8     'h26
    [1]       integral        8     'h78
    [2]       integral        8     'h4e
    [3]       integral        8     'hae
    [4]       integral        8     'hb9
    ...       ...             ...   ...
    [55]      integral        8     'h6e
    [56]      integral        8     'h8b
    [57]      integral        8     'hb3
    [58]      integral        8     'hfe
    [59]      integral        8     'h6b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 120100000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 120300000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 135500000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 135500000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5119
  dmac                         integral        48    'h9b8ae73bdbb1
  smac                         integral        48    'h7b0a68730f74
  ether_type                   integral        16    'hca7d
  pload                        da(integral)    60    -
    [0]                        integral        8     'h84
    [1]                        integral        8     'h53
    [2]                        integral        8     'ha9
    [3]                        integral        8     'hb5
    [4]                        integral        8     'h67
    ...                        ...             ...   ...
    [55]                       integral        8     'h35
    [56]                       integral        8     'hac
    [57]                       integral        8     'hcb
    [58]                       integral        8     'hca
    [59]                       integral        8     'h62
  crc                          integral        32    'h0
  begin_time                   time            64    135500000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 135700000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5057
  dmac        integral        48    'hd18584ab61da
  smac        integral        48    'h411db14b6b43
  ether_type  integral        16    'h77d7
  pload       da(integral)    60    -
    [0]       integral        8     'h8d
    [1]       integral        8     'ha7
    [2]       integral        8     'h34
    [3]       integral        8     'hd
    [4]       integral        8     'h5d
    ...       ...             ...   ...
    [55]      integral        8     'h38
    [56]      integral        8     'hc9
    [57]      integral        8     'h39
    [58]      integral        8     'hcc
    [59]      integral        8     'h6c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 135700000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5063
  dmac        integral        48    'hd18584ab61da
  smac        integral        48    'h411db14b6b43
  ether_type  integral        16    'h77d7
  pload       da(integral)    60    -
    [0]       integral        8     'h8d
    [1]       integral        8     'ha7
    [2]       integral        8     'h34
    [3]       integral        8     'hd
    [4]       integral        8     'h5d
    ...       ...             ...   ...
    [55]      integral        8     'h38
    [56]      integral        8     'hc9
    [57]      integral        8     'h39
    [58]      integral        8     'hcc
    [59]      integral        8     'h6c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 135900000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5115
  dmac        integral        48    'hd18584ab61da
  smac        integral        48    'h411db14b6b43
  ether_type  integral        16    'h77d7
  pload       da(integral)    60    -
    [0]       integral        8     'h8d
    [1]       integral        8     'ha7
    [2]       integral        8     'h34
    [3]       integral        8     'hd
    [4]       integral        8     'h5d
    ...       ...             ...   ...
    [55]      integral        8     'h38
    [56]      integral        8     'hc9
    [57]      integral        8     'h39
    [58]      integral        8     'hcc
    [59]      integral        8     'h6c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 135900000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5115
  dmac        integral        48    'hd18584ab61da
  smac        integral        48    'h411db14b6b43
  ether_type  integral        16    'h77d7
  pload       da(integral)    60    -
    [0]       integral        8     'h8d
    [1]       integral        8     'ha7
    [2]       integral        8     'h34
    [3]       integral        8     'hd
    [4]       integral        8     'h5d
    ...       ...             ...   ...
    [55]      integral        8     'h38
    [56]      integral        8     'hc9
    [57]      integral        8     'h39
    [58]      integral        8     'hcc
    [59]      integral        8     'h6c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 136900000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 137100000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 152300000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(43) @ 152300000: uvm_test_top.env.i_agt.drv [my_driver] begin to drive one pkt
----------------------------------------------------------------------------------------------
Name                           Type            Size  Value
----------------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5137
  dmac                         integral        48    'h3b49ab14263d
  smac                         integral        48    'hfeae4d2b714b
  ether_type                   integral        16    'hcc
  pload                        da(integral)    60    -
    [0]                        integral        8     'h11
    [1]                        integral        8     'h3
    [2]                        integral        8     'h68
    [3]                        integral        8     'h86
    [4]                        integral        8     'h8
    ...                        ...             ...   ...
    [55]                       integral        8     'h74
    [56]                       integral        8     'hd9
    [57]                       integral        8     'h10
    [58]                       integral        8     'h51
    [59]                       integral        8     'h4d
  crc                          integral        32    'h0
  begin_time                   time            64    152300000
  depth                        int             32    'd2
  parent sequence (name)       string          14    case1_sequence
  parent sequence (full name)  string          41    uvm_test_top.env.i_agt.sqr.case1_sequence
  sequencer                    string          26    uvm_test_top.env.i_agt.sqr
----------------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 152500000: uvm_test_top.env.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5146
  dmac        integral        48    'h9b8ae73bdbb1
  smac        integral        48    'h7b0a68730f74
  ether_type  integral        16    'hca7d
  pload       da(integral)    60    -
    [0]       integral        8     'h84
    [1]       integral        8     'h53
    [2]       integral        8     'ha9
    [3]       integral        8     'hb5
    [4]       integral        8     'h67
    ...       ...             ...   ...
    [55]      integral        8     'h35
    [56]      integral        8     'hac
    [57]      integral        8     'hcb
    [58]      integral        8     'hca
    [59]      integral        8     'h62
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 152500000: uvm_test_top.env.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5078
  dmac        integral        48    'h9b8ae73bdbb1
  smac        integral        48    'h7b0a68730f74
  ether_type  integral        16    'hca7d
  pload       da(integral)    60    -
    [0]       integral        8     'h84
    [1]       integral        8     'h53
    [2]       integral        8     'ha9
    [3]       integral        8     'hb5
    [4]       integral        8     'h67
    ...       ...             ...   ...
    [55]      integral        8     'h35
    [56]      integral        8     'hac
    [57]      integral        8     'hcb
    [58]      integral        8     'hca
    [59]      integral        8     'h62
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 152700000: uvm_test_top.env.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5027
  dmac        integral        48    'h9b8ae73bdbb1
  smac        integral        48    'h7b0a68730f74
  ether_type  integral        16    'hca7d
  pload       da(integral)    60    -
    [0]       integral        8     'h84
    [1]       integral        8     'h53
    [2]       integral        8     'ha9
    [3]       integral        8     'hb5
    [4]       integral        8     'h67
    ...       ...             ...   ...
    [55]      integral        8     'h35
    [56]      integral        8     'hac
    [57]      integral        8     'hcb
    [58]      integral        8     'hca
    [59]      integral        8     'h62
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 152700000: uvm_test_top.env.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5027
  dmac        integral        48    'h9b8ae73bdbb1
  smac        integral        48    'h7b0a68730f74
  ether_type  integral        16    'hca7d
  pload       da(integral)    60    -
    [0]       integral        8     'h84
    [1]       integral        8     'h53
    [2]       integral        8     'ha9
    [3]       integral        8     'hb5
    [4]       integral        8     'h67
    ...       ...             ...   ...
    [55]      integral        8     'h35
    [56]      integral        8     'hac
    [57]      integral        8     'hcb
    [58]      integral        8     'hca
    [59]      integral        8     'h62
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 153700000: uvm_test_top.env.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 153900000: uvm_test_top.env.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 169100000: uvm_test_top.env.i_agt.drv [my_driver] end drive one pkt
TEST CASE PASSED
```
