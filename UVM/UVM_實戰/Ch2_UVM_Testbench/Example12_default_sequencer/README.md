# xrun.log
```
UVM_INFO my_env.sv(16) @ 0: uvm_test_top [my_env] my_envs is new
UVM_INFO @ 0: reporter [RNTST] Running test my_env...
UVM_INFO my_env.sv(21) @ 0: uvm_test_top [my_env] my_env build phase!!
UVM_INFO my_model.sv(14) @ 0: uvm_test_top.mdl [my_model] my_model is new
UVM_INFO my_agent.sv(24) @ 0: uvm_test_top.i_agt [my_agent] my_agent is new (active)
UVM_INFO my_driver.sv(9) @ 0: uvm_test_top.i_agt.drv [my_driver] new is called
UVM_INFO my_driver.sv(17) @ 0: uvm_test_top.i_agt.drv [my_driver] build_phase is called
UVM_INFO my_driver.sv(21) @ 0: uvm_test_top.i_agt.drv [my_driver] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.i_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_model.sv(19) @ 0: uvm_test_top.mdl [my_model] main_phase is called
UVM_INFO my_agent.sv(26) @ 0: uvm_test_top.o_agt [my_agent] my_agent is new (passive)
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.o_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.o_agt.mon [my_monitor] main_phase is called
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.i_agt.mon [my_monitor] main_phase is called
UVM_INFO my_sequence.sv(30) @ 0: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 1
UVM_INFO my_driver.sv(43) @ 1100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @4951
  dmac                         integral        48    'he5363bc514b9
  smac                         integral        48    'h4d0d584b145c
  ether_type                   integral        16    'h1ddf
  pload                        da(integral)    1483  -
    [0]                        integral        8     'hfd
    [1]                        integral        8     'hbc
    [2]                        integral        8     'hfc
    [3]                        integral        8     'hd4
    [4]                        integral        8     'hec
    ...                        ...             ...   ...
    [1478]                     integral        8     'h12
    [1479]                     integral        8     'h7e
    [1480]                     integral        8     'hb7
    [1481]                     integral        8     'h39
    [1482]                     integral        8     'h5c
  crc                          integral        32    'h0
  begin_time                   time            64    1100000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 2500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 2700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 302500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 302500000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 2
UVM_INFO my_driver.sv(43) @ 302500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5066
  dmac                         integral        48    'h221dfe9c410c
  smac                         integral        48    'hcb0f5e813d65
  ether_type                   integral        16    'h9d75
  pload                        da(integral)    934   -
    [0]                        integral        8     'hb
    [1]                        integral        8     'h76
    [2]                        integral        8     'ha8
    [3]                        integral        8     'hda
    [4]                        integral        8     'hc2
    ...                        ...             ...   ...
    [929]                      integral        8     'h10
    [930]                      integral        8     'ha0
    [931]                      integral        8     'hbe
    [932]                      integral        8     'h68
    [933]                      integral        8     'h72
  crc                          integral        32    'h0
  begin_time                   time            64    302500000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 302700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4940
  dmac        integral        48    'he5363bc514b9
  smac        integral        48    'h4d0d584b145c
  ether_type  integral        16    'h1ddf
  pload       da(integral)    1483  -
    [0]       integral        8     'hfd
    [1]       integral        8     'hbc
    [2]       integral        8     'hfc
    [3]       integral        8     'hd4
    [4]       integral        8     'hec
    ...       ...             ...   ...
    [1478]    integral        8     'h12
    [1479]    integral        8     'h7e
    [1480]    integral        8     'hb7
    [1481]    integral        8     'h39
    [1482]    integral        8     'h5c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 302700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5019
  dmac        integral        48    'he5363bc514b9
  smac        integral        48    'h4d0d584b145c
  ether_type  integral        16    'h1ddf
  pload       da(integral)    1483  -
    [0]       integral        8     'hfd
    [1]       integral        8     'hbc
    [2]       integral        8     'hfc
    [3]       integral        8     'hd4
    [4]       integral        8     'hec
    ...       ...             ...   ...
    [1478]    integral        8     'h12
    [1479]    integral        8     'h7e
    [1480]    integral        8     'hb7
    [1481]    integral        8     'h39
    [1482]    integral        8     'h5c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 302900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4907
  dmac        integral        48    'he5363bc514b9
  smac        integral        48    'h4d0d584b145c
  ether_type  integral        16    'h1ddf
  pload       da(integral)    1483  -
    [0]       integral        8     'hfd
    [1]       integral        8     'hbc
    [2]       integral        8     'hfc
    [3]       integral        8     'hd4
    [4]       integral        8     'hec
    ...       ...             ...   ...
    [1478]    integral        8     'h12
    [1479]    integral        8     'h7e
    [1480]    integral        8     'hb7
    [1481]    integral        8     'h39
    [1482]    integral        8     'h5c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 302900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4907
  dmac        integral        48    'he5363bc514b9
  smac        integral        48    'h4d0d584b145c
  ether_type  integral        16    'h1ddf
  pload       da(integral)    1483  -
    [0]       integral        8     'hfd
    [1]       integral        8     'hbc
    [2]       integral        8     'hfc
    [3]       integral        8     'hd4
    [4]       integral        8     'hec
    ...       ...             ...   ...
    [1478]    integral        8     'h12
    [1479]    integral        8     'h7e
    [1480]    integral        8     'hb7
    [1481]    integral        8     'h39
    [1482]    integral        8     'h5c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 303900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 304100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 494100000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 494100000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 3
UVM_INFO my_driver.sv(43) @ 494100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5062
  dmac                         integral        48    'h42857fb17d4
  smac                         integral        48    'h949140a4afc6
  ether_type                   integral        16    'hab23
  pload                        da(integral)    318   -
    [0]                        integral        8     'hd
    [1]                        integral        8     'h57
    [2]                        integral        8     'h7c
    [3]                        integral        8     'h8f
    [4]                        integral        8     'h5b
    ...                        ...             ...   ...
    [313]                      integral        8     'h49
    [314]                      integral        8     'h5b
    [315]                      integral        8     'hbb
    [316]                      integral        8     'hfd
    [317]                      integral        8     'h73
  crc                          integral        32    'h0
  begin_time                   time            64    494100000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 494300000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4932
  dmac        integral        48    'h221dfe9c410c
  smac        integral        48    'hcb0f5e813d65
  ether_type  integral        16    'h9d75
  pload       da(integral)    934   -
    [0]       integral        8     'hb
    [1]       integral        8     'h76
    [2]       integral        8     'ha8
    [3]       integral        8     'hda
    [4]       integral        8     'hc2
    ...       ...             ...   ...
    [929]     integral        8     'h10
    [930]     integral        8     'ha0
    [931]     integral        8     'hbe
    [932]     integral        8     'h68
    [933]     integral        8     'h72
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 494300000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4939
  dmac        integral        48    'h221dfe9c410c
  smac        integral        48    'hcb0f5e813d65
  ether_type  integral        16    'h9d75
  pload       da(integral)    934   -
    [0]       integral        8     'hb
    [1]       integral        8     'h76
    [2]       integral        8     'ha8
    [3]       integral        8     'hda
    [4]       integral        8     'hc2
    ...       ...             ...   ...
    [929]     integral        8     'h10
    [930]     integral        8     'ha0
    [931]     integral        8     'hbe
    [932]     integral        8     'h68
    [933]     integral        8     'h72
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 494500000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4916
  dmac        integral        48    'h221dfe9c410c
  smac        integral        48    'hcb0f5e813d65
  ether_type  integral        16    'h9d75
  pload       da(integral)    934   -
    [0]       integral        8     'hb
    [1]       integral        8     'h76
    [2]       integral        8     'ha8
    [3]       integral        8     'hda
    [4]       integral        8     'hc2
    ...       ...             ...   ...
    [929]     integral        8     'h10
    [930]     integral        8     'ha0
    [931]     integral        8     'hbe
    [932]     integral        8     'h68
    [933]     integral        8     'h72
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 494500000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4916
  dmac        integral        48    'h221dfe9c410c
  smac        integral        48    'hcb0f5e813d65
  ether_type  integral        16    'h9d75
  pload       da(integral)    934   -
    [0]       integral        8     'hb
    [1]       integral        8     'h76
    [2]       integral        8     'ha8
    [3]       integral        8     'hda
    [4]       integral        8     'hc2
    ...       ...             ...   ...
    [929]     integral        8     'h10
    [930]     integral        8     'ha0
    [931]     integral        8     'hbe
    [932]     integral        8     'h68
    [933]     integral        8     'h72
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 495500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 495700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 562500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 562500000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 4
UVM_INFO my_driver.sv(43) @ 562500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5066
  dmac                         integral        48    'h26629340b36
  smac                         integral        48    'h138b267606da
  ether_type                   integral        16    'h6862
  pload                        da(integral)    60    -
    [0]                        integral        8     'hbd
    [1]                        integral        8     'h18
    [2]                        integral        8     'h4c
    [3]                        integral        8     'h8a
    [4]                        integral        8     'hd8
    ...                        ...             ...   ...
    [55]                       integral        8     'h14
    [56]                       integral        8     'h88
    [57]                       integral        8     'h5a
    [58]                       integral        8     'h96
    [59]                       integral        8     'hf8
  crc                          integral        32    'h0
  begin_time                   time            64    562500000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 562700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5046
  dmac        integral        48    'h42857fb17d4
  smac        integral        48    'h949140a4afc6
  ether_type  integral        16    'hab23
  pload       da(integral)    318   -
    [0]       integral        8     'hd
    [1]       integral        8     'h57
    [2]       integral        8     'h7c
    [3]       integral        8     'h8f
    [4]       integral        8     'h5b
    ...       ...             ...   ...
    [313]     integral        8     'h49
    [314]     integral        8     'h5b
    [315]     integral        8     'hbb
    [316]     integral        8     'hfd
    [317]     integral        8     'h73
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 562700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4941
  dmac        integral        48    'h42857fb17d4
  smac        integral        48    'h949140a4afc6
  ether_type  integral        16    'hab23
  pload       da(integral)    318   -
    [0]       integral        8     'hd
    [1]       integral        8     'h57
    [2]       integral        8     'h7c
    [3]       integral        8     'h8f
    [4]       integral        8     'h5b
    ...       ...             ...   ...
    [313]     integral        8     'h49
    [314]     integral        8     'h5b
    [315]     integral        8     'hbb
    [316]     integral        8     'hfd
    [317]     integral        8     'h73
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 562900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5039
  dmac        integral        48    'h42857fb17d4
  smac        integral        48    'h949140a4afc6
  ether_type  integral        16    'hab23
  pload       da(integral)    318   -
    [0]       integral        8     'hd
    [1]       integral        8     'h57
    [2]       integral        8     'h7c
    [3]       integral        8     'h8f
    [4]       integral        8     'h5b
    ...       ...             ...   ...
    [313]     integral        8     'h49
    [314]     integral        8     'h5b
    [315]     integral        8     'hbb
    [316]     integral        8     'hfd
    [317]     integral        8     'h73
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 562900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5039
  dmac        integral        48    'h42857fb17d4
  smac        integral        48    'h949140a4afc6
  ether_type  integral        16    'hab23
  pload       da(integral)    318   -
    [0]       integral        8     'hd
    [1]       integral        8     'h57
    [2]       integral        8     'h7c
    [3]       integral        8     'h8f
    [4]       integral        8     'h5b
    ...       ...             ...   ...
    [313]     integral        8     'h49
    [314]     integral        8     'h5b
    [315]     integral        8     'hbb
    [316]     integral        8     'hfd
    [317]     integral        8     'h73
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 563900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 564100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 579300000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 579300000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 5
UVM_INFO my_driver.sv(43) @ 579300000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5062
  dmac                         integral        48    'h9a9f2569af17
  smac                         integral        48    'h2c39917290a5
  ether_type                   integral        16    'he195
  pload                        da(integral)    1490  -
    [0]                        integral        8     'h3c
    [1]                        integral        8     'hbc
    [2]                        integral        8     'h8f
    [3]                        integral        8     'h13
    [4]                        integral        8     'hb2
    ...                        ...             ...   ...
    [1485]                     integral        8     'ha9
    [1486]                     integral        8     'h3e
    [1487]                     integral        8     'h19
    [1488]                     integral        8     'h8
    [1489]                     integral        8     'ha9
  crc                          integral        32    'h0
  begin_time                   time            64    579300000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 579500000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4996
  dmac        integral        48    'h26629340b36
  smac        integral        48    'h138b267606da
  ether_type  integral        16    'h6862
  pload       da(integral)    60    -
    [0]       integral        8     'hbd
    [1]       integral        8     'h18
    [2]       integral        8     'h4c
    [3]       integral        8     'h8a
    [4]       integral        8     'hd8
    ...       ...             ...   ...
    [55]      integral        8     'h14
    [56]      integral        8     'h88
    [57]      integral        8     'h5a
    [58]      integral        8     'h96
    [59]      integral        8     'hf8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 579500000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5020
  dmac        integral        48    'h26629340b36
  smac        integral        48    'h138b267606da
  ether_type  integral        16    'h6862
  pload       da(integral)    60    -
    [0]       integral        8     'hbd
    [1]       integral        8     'h18
    [2]       integral        8     'h4c
    [3]       integral        8     'h8a
    [4]       integral        8     'hd8
    ...       ...             ...   ...
    [55]      integral        8     'h14
    [56]      integral        8     'h88
    [57]      integral        8     'h5a
    [58]      integral        8     'h96
    [59]      integral        8     'hf8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 579700000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5083
  dmac        integral        48    'h26629340b36
  smac        integral        48    'h138b267606da
  ether_type  integral        16    'h6862
  pload       da(integral)    60    -
    [0]       integral        8     'hbd
    [1]       integral        8     'h18
    [2]       integral        8     'h4c
    [3]       integral        8     'h8a
    [4]       integral        8     'hd8
    ...       ...             ...   ...
    [55]      integral        8     'h14
    [56]      integral        8     'h88
    [57]      integral        8     'h5a
    [58]      integral        8     'h96
    [59]      integral        8     'hf8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 579700000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5083
  dmac        integral        48    'h26629340b36
  smac        integral        48    'h138b267606da
  ether_type  integral        16    'h6862
  pload       da(integral)    60    -
    [0]       integral        8     'hbd
    [1]       integral        8     'h18
    [2]       integral        8     'h4c
    [3]       integral        8     'h8a
    [4]       integral        8     'hd8
    ...       ...             ...   ...
    [55]      integral        8     'h14
    [56]      integral        8     'h88
    [57]      integral        8     'h5a
    [58]      integral        8     'h96
    [59]      integral        8     'hf8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 580700000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 580900000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 882100000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 882100000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 6
UVM_INFO my_driver.sv(43) @ 882100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5066
  dmac                         integral        48    'h3c0be86025e4
  smac                         integral        48    'h779ffe308148
  ether_type                   integral        16    'h4b93
  pload                        da(integral)    1058  -
    [0]                        integral        8     'h85
    [1]                        integral        8     'h4b
    [2]                        integral        8     'ha6
    [3]                        integral        8     'h3b
    [4]                        integral        8     'hda
    ...                        ...             ...   ...
    [1053]                     integral        8     'hfa
    [1054]                     integral        8     'h2
    [1055]                     integral        8     'h69
    [1056]                     integral        8     'h7e
    [1057]                     integral        8     'he2
  crc                          integral        32    'h0
  begin_time                   time            64    882100000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 882300000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4992
  dmac        integral        48    'h9a9f2569af17
  smac        integral        48    'h2c39917290a5
  ether_type  integral        16    'he195
  pload       da(integral)    1490  -
    [0]       integral        8     'h3c
    [1]       integral        8     'hbc
    [2]       integral        8     'h8f
    [3]       integral        8     'h13
    [4]       integral        8     'hb2
    ...       ...             ...   ...
    [1485]    integral        8     'ha9
    [1486]    integral        8     'h3e
    [1487]    integral        8     'h19
    [1488]    integral        8     'h8
    [1489]    integral        8     'ha9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 882300000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4977
  dmac        integral        48    'h9a9f2569af17
  smac        integral        48    'h2c39917290a5
  ether_type  integral        16    'he195
  pload       da(integral)    1490  -
    [0]       integral        8     'h3c
    [1]       integral        8     'hbc
    [2]       integral        8     'h8f
    [3]       integral        8     'h13
    [4]       integral        8     'hb2
    ...       ...             ...   ...
    [1485]    integral        8     'ha9
    [1486]    integral        8     'h3e
    [1487]    integral        8     'h19
    [1488]    integral        8     'h8
    [1489]    integral        8     'ha9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 882500000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'h9a9f2569af17
  smac        integral        48    'h2c39917290a5
  ether_type  integral        16    'he195
  pload       da(integral)    1490  -
    [0]       integral        8     'h3c
    [1]       integral        8     'hbc
    [2]       integral        8     'h8f
    [3]       integral        8     'h13
    [4]       integral        8     'hb2
    ...       ...             ...   ...
    [1485]    integral        8     'ha9
    [1486]    integral        8     'h3e
    [1487]    integral        8     'h19
    [1488]    integral        8     'h8
    [1489]    integral        8     'ha9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 882500000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5094
  dmac        integral        48    'h9a9f2569af17
  smac        integral        48    'h2c39917290a5
  ether_type  integral        16    'he195
  pload       da(integral)    1490  -
    [0]       integral        8     'h3c
    [1]       integral        8     'hbc
    [2]       integral        8     'h8f
    [3]       integral        8     'h13
    [4]       integral        8     'hb2
    ...       ...             ...   ...
    [1485]    integral        8     'ha9
    [1486]    integral        8     'h3e
    [1487]    integral        8     'h19
    [1488]    integral        8     'h8
    [1489]    integral        8     'ha9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 883500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 883700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1098500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 1098500000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 7
UVM_INFO my_driver.sv(43) @ 1098500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5062
  dmac                         integral        48    'h272cd8e75a57
  smac                         integral        48    'h4799d58a5594
  ether_type                   integral        16    'h2e96
  pload                        da(integral)    43    -
    [0]                        integral        8     'h17
    [1]                        integral        8     'h1
    [2]                        integral        8     'h56
    [3]                        integral        8     'h36
    [4]                        integral        8     'h15
    ...                        ...             ...   ...
    [38]                       integral        8     'h41
    [39]                       integral        8     'h27
    [40]                       integral        8     'h44
    [41]                       integral        8     'h60
    [42]                       integral        8     'h1b
  crc                          integral        32    'h0
  begin_time                   time            64    1098500000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1098700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4973
  dmac        integral        48    'h3c0be86025e4
  smac        integral        48    'h779ffe308148
  ether_type  integral        16    'h4b93
  pload       da(integral)    1058  -
    [0]       integral        8     'h85
    [1]       integral        8     'h4b
    [2]       integral        8     'ha6
    [3]       integral        8     'h3b
    [4]       integral        8     'hda
    ...       ...             ...   ...
    [1053]    integral        8     'hfa
    [1054]    integral        8     'h2
    [1055]    integral        8     'h69
    [1056]    integral        8     'h7e
    [1057]    integral        8     'he2
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1098700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5028
  dmac        integral        48    'h3c0be86025e4
  smac        integral        48    'h779ffe308148
  ether_type  integral        16    'h4b93
  pload       da(integral)    1058  -
    [0]       integral        8     'h85
    [1]       integral        8     'h4b
    [2]       integral        8     'ha6
    [3]       integral        8     'h3b
    [4]       integral        8     'hda
    ...       ...             ...   ...
    [1053]    integral        8     'hfa
    [1054]    integral        8     'h2
    [1055]    integral        8     'h69
    [1056]    integral        8     'h7e
    [1057]    integral        8     'he2
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1098900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5058
  dmac        integral        48    'h3c0be86025e4
  smac        integral        48    'h779ffe308148
  ether_type  integral        16    'h4b93
  pload       da(integral)    1058  -
    [0]       integral        8     'h85
    [1]       integral        8     'h4b
    [2]       integral        8     'ha6
    [3]       integral        8     'h3b
    [4]       integral        8     'hda
    ...       ...             ...   ...
    [1053]    integral        8     'hfa
    [1054]    integral        8     'h2
    [1055]    integral        8     'h69
    [1056]    integral        8     'h7e
    [1057]    integral        8     'he2
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1098900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5058
  dmac        integral        48    'h3c0be86025e4
  smac        integral        48    'h779ffe308148
  ether_type  integral        16    'h4b93
  pload       da(integral)    1058  -
    [0]       integral        8     'h85
    [1]       integral        8     'h4b
    [2]       integral        8     'ha6
    [3]       integral        8     'h3b
    [4]       integral        8     'hda
    ...       ...             ...   ...
    [1053]    integral        8     'hfa
    [1054]    integral        8     'h2
    [1055]    integral        8     'h69
    [1056]    integral        8     'h7e
    [1057]    integral        8     'he2
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1099900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1100100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1111900000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 1111900000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 8
UVM_INFO my_driver.sv(43) @ 1111900000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5066
  dmac                         integral        48    'hee6f60ee92fa
  smac                         integral        48    'h9dffa540067f
  ether_type                   integral        16    'h7c5
  pload                        da(integral)    1353  -
    [0]                        integral        8     'hfd
    [1]                        integral        8     'h60
    [2]                        integral        8     'hfa
    [3]                        integral        8     'h4d
    [4]                        integral        8     'h4e
    ...                        ...             ...   ...
    [1348]                     integral        8     'h5e
    [1349]                     integral        8     'hcb
    [1350]                     integral        8     'hb8
    [1351]                     integral        8     'hdb
    [1352]                     integral        8     'h20
  crc                          integral        32    'h0
  begin_time                   time            64    1111900000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1112100000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4989
  dmac        integral        48    'h272cd8e75a57
  smac        integral        48    'h4799d58a5594
  ether_type  integral        16    'h2e96
  pload       da(integral)    43    -
    [0]       integral        8     'h17
    [1]       integral        8     'h1
    [2]       integral        8     'h56
    [3]       integral        8     'h36
    [4]       integral        8     'h15
    ...       ...             ...   ...
    [38]      integral        8     'h41
    [39]      integral        8     'h27
    [40]      integral        8     'h44
    [41]      integral        8     'h60
    [42]      integral        8     'h1b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1112100000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4981
  dmac        integral        48    'h272cd8e75a57
  smac        integral        48    'h4799d58a5594
  ether_type  integral        16    'h2e96
  pload       da(integral)    43    -
    [0]       integral        8     'h17
    [1]       integral        8     'h1
    [2]       integral        8     'h56
    [3]       integral        8     'h36
    [4]       integral        8     'h15
    ...       ...             ...   ...
    [38]      integral        8     'h41
    [39]      integral        8     'h27
    [40]      integral        8     'h44
    [41]      integral        8     'h60
    [42]      integral        8     'h1b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1112300000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5100
  dmac        integral        48    'h272cd8e75a57
  smac        integral        48    'h4799d58a5594
  ether_type  integral        16    'h2e96
  pload       da(integral)    43    -
    [0]       integral        8     'h17
    [1]       integral        8     'h1
    [2]       integral        8     'h56
    [3]       integral        8     'h36
    [4]       integral        8     'h15
    ...       ...             ...   ...
    [38]      integral        8     'h41
    [39]      integral        8     'h27
    [40]      integral        8     'h44
    [41]      integral        8     'h60
    [42]      integral        8     'h1b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1112300000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5100
  dmac        integral        48    'h272cd8e75a57
  smac        integral        48    'h4799d58a5594
  ether_type  integral        16    'h2e96
  pload       da(integral)    43    -
    [0]       integral        8     'h17
    [1]       integral        8     'h1
    [2]       integral        8     'h56
    [3]       integral        8     'h36
    [4]       integral        8     'h15
    ...       ...             ...   ...
    [38]      integral        8     'h41
    [39]      integral        8     'h27
    [40]      integral        8     'h44
    [41]      integral        8     'h60
    [42]      integral        8     'h1b
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1113300000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1113500000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1387300000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 1387300000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 9
UVM_INFO my_driver.sv(43) @ 1387300000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5062
  dmac                         integral        48    'h372bb4e4873a
  smac                         integral        48    'h5924b0b9285d
  ether_type                   integral        16    'h50f7
  pload                        da(integral)    425   -
    [0]                        integral        8     'h71
    [1]                        integral        8     'h72
    [2]                        integral        8     'h8
    [3]                        integral        8     'h4
    [4]                        integral        8     'h41
    ...                        ...             ...   ...
    [420]                      integral        8     'h52
    [421]                      integral        8     'h28
    [422]                      integral        8     'hc7
    [423]                      integral        8     'h0
    [424]                      integral        8     'h76
  crc                          integral        32    'h0
  begin_time                   time            64    1387300000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1387500000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5002
  dmac        integral        48    'hee6f60ee92fa
  smac        integral        48    'h9dffa540067f
  ether_type  integral        16    'h7c5
  pload       da(integral)    1353  -
    [0]       integral        8     'hfd
    [1]       integral        8     'h60
    [2]       integral        8     'hfa
    [3]       integral        8     'h4d
    [4]       integral        8     'h4e
    ...       ...             ...   ...
    [1348]    integral        8     'h5e
    [1349]    integral        8     'hcb
    [1350]    integral        8     'hb8
    [1351]    integral        8     'hdb
    [1352]    integral        8     'h20
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1387500000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5008
  dmac        integral        48    'hee6f60ee92fa
  smac        integral        48    'h9dffa540067f
  ether_type  integral        16    'h7c5
  pload       da(integral)    1353  -
    [0]       integral        8     'hfd
    [1]       integral        8     'h60
    [2]       integral        8     'hfa
    [3]       integral        8     'h4d
    [4]       integral        8     'h4e
    ...       ...             ...   ...
    [1348]    integral        8     'h5e
    [1349]    integral        8     'hcb
    [1350]    integral        8     'hb8
    [1351]    integral        8     'hdb
    [1352]    integral        8     'h20
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1387700000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5060
  dmac        integral        48    'hee6f60ee92fa
  smac        integral        48    'h9dffa540067f
  ether_type  integral        16    'h7c5
  pload       da(integral)    1353  -
    [0]       integral        8     'hfd
    [1]       integral        8     'h60
    [2]       integral        8     'hfa
    [3]       integral        8     'h4d
    [4]       integral        8     'h4e
    ...       ...             ...   ...
    [1348]    integral        8     'h5e
    [1349]    integral        8     'hcb
    [1350]    integral        8     'hb8
    [1351]    integral        8     'hdb
    [1352]    integral        8     'h20
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1387700000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5060
  dmac        integral        48    'hee6f60ee92fa
  smac        integral        48    'h9dffa540067f
  ether_type  integral        16    'h7c5
  pload       da(integral)    1353  -
    [0]       integral        8     'hfd
    [1]       integral        8     'h60
    [2]       integral        8     'hfa
    [3]       integral        8     'h4d
    [4]       integral        8     'h4e
    ...       ...             ...   ...
    [1348]    integral        8     'h5e
    [1349]    integral        8     'hcb
    [1350]    integral        8     'hb8
    [1351]    integral        8     'hdb
    [1352]    integral        8     'h20
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1388700000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1388900000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1477100000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(30) @ 1477100000: uvm_test_top.i_agt.sqr@@my_sequence [my_sequence] transaction: 10
UVM_INFO my_driver.sv(43) @ 1477100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
---------------------------------------------------------------------------------------
Name                           Type            Size  Value
---------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5066
  dmac                         integral        48    'h9901ed4426f8
  smac                         integral        48    'h8f74a248ac01
  ether_type                   integral        16    'h8883
  pload                        da(integral)    1077  -
    [0]                        integral        8     'h21
    [1]                        integral        8     'h30
    [2]                        integral        8     'hd8
    [3]                        integral        8     'ha5
    [4]                        integral        8     'ha
    ...                        ...             ...   ...
    [1072]                     integral        8     'hc3
    [1073]                     integral        8     'h4f
    [1074]                     integral        8     'h17
    [1075]                     integral        8     'h2f
    [1076]                     integral        8     'h88
  crc                          integral        32    'h0
  begin_time                   time            64    1477100000
  depth                        int             32    'd2
  parent sequence (name)       string          11    my_sequence
  parent sequence (full name)  string          34    uvm_test_top.i_agt.sqr.my_sequence
  sequencer                    string          22    uvm_test_top.i_agt.sqr
---------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1477300000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5091
  dmac        integral        48    'h372bb4e4873a
  smac        integral        48    'h5924b0b9285d
  ether_type  integral        16    'h50f7
  pload       da(integral)    425   -
    [0]       integral        8     'h71
    [1]       integral        8     'h72
    [2]       integral        8     'h8
    [3]       integral        8     'h4
    [4]       integral        8     'h41
    ...       ...             ...   ...
    [420]     integral        8     'h52
    [421]     integral        8     'h28
    [422]     integral        8     'hc7
    [423]     integral        8     'h0
    [424]     integral        8     'h76
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1477300000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5023
  dmac        integral        48    'h372bb4e4873a
  smac        integral        48    'h5924b0b9285d
  ether_type  integral        16    'h50f7
  pload       da(integral)    425   -
    [0]       integral        8     'h71
    [1]       integral        8     'h72
    [2]       integral        8     'h8
    [3]       integral        8     'h4
    [4]       integral        8     'h41
    ...       ...             ...   ...
    [420]     integral        8     'h52
    [421]     integral        8     'h28
    [422]     integral        8     'hc7
    [423]     integral        8     'h0
    [424]     integral        8     'h76
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1477500000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4972
  dmac        integral        48    'h372bb4e4873a
  smac        integral        48    'h5924b0b9285d
  ether_type  integral        16    'h50f7
  pload       da(integral)    425   -
    [0]       integral        8     'h71
    [1]       integral        8     'h72
    [2]       integral        8     'h8
    [3]       integral        8     'h4
    [4]       integral        8     'h41
    ...       ...             ...   ...
    [420]     integral        8     'h52
    [421]     integral        8     'h28
    [422]     integral        8     'hc7
    [423]     integral        8     'h0
    [424]     integral        8     'h76
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1477500000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4972
  dmac        integral        48    'h372bb4e4873a
  smac        integral        48    'h5924b0b9285d
  ether_type  integral        16    'h50f7
  pload       da(integral)    425   -
    [0]       integral        8     'h71
    [1]       integral        8     'h72
    [2]       integral        8     'h8
    [3]       integral        8     'h4
    [4]       integral        8     'h41
    ...       ...             ...   ...
    [420]     integral        8     'h52
    [421]     integral        8     'h28
    [422]     integral        8     'hc7
    [423]     integral        8     'h0
    [424]     integral        8     'h76
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1478500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1478700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(54) @ 1697300000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(63) @ 1697500000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4931
  dmac        integral        48    'h9901ed4426f8
  smac        integral        48    'h8f74a248ac01
  ether_type  integral        16    'h8883
  pload       da(integral)    1077  -
    [0]       integral        8     'h21
    [1]       integral        8     'h30
    [2]       integral        8     'hd8
    [3]       integral        8     'ha5
    [4]       integral        8     'ha
    ...       ...             ...   ...
    [1072]    integral        8     'hc3
    [1073]    integral        8     'h4f
    [1074]    integral        8     'h17
    [1075]    integral        8     'h2f
    [1076]    integral        8     'h88
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(32) @ 1697500000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5084
  dmac        integral        48    'h9901ed4426f8
  smac        integral        48    'h8f74a248ac01
  ether_type  integral        16    'h8883
  pload       da(integral)    1077  -
    [0]       integral        8     'h21
    [1]       integral        8     'h30
    [2]       integral        8     'hd8
    [3]       integral        8     'ha5
    [4]       integral        8     'ha
    ...       ...             ...   ...
    [1072]    integral        8     'hc3
    [1073]    integral        8     'h4f
    [1074]    integral        8     'h17
    [1075]    integral        8     'h2f
    [1076]    integral        8     'h88
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1697700000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4993
  dmac        integral        48    'h9901ed4426f8
  smac        integral        48    'h8f74a248ac01
  ether_type  integral        16    'h8883
  pload       da(integral)    1077  -
    [0]       integral        8     'h21
    [1]       integral        8     'h30
    [2]       integral        8     'hd8
    [3]       integral        8     'ha5
    [4]       integral        8     'ha
    ...       ...             ...   ...
    [1072]    integral        8     'hc3
    [1073]    integral        8     'h4f
    [1074]    integral        8     'h17
    [1075]    integral        8     'h2f
    [1076]    integral        8     'h88
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 1697700000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4993
  dmac        integral        48    'h9901ed4426f8
  smac        integral        48    'h8f74a248ac01
  ether_type  integral        16    'h8883
  pload       da(integral)    1077  -
    [0]       integral        8     'h21
    [1]       integral        8     'h30
    [2]       integral        8     'hd8
    [3]       integral        8     'ha5
    [4]       integral        8     'ha
    ...       ...             ...   ...
    [1072]    integral        8     'hc3
    [1073]    integral        8     'h4f
    [1074]    integral        8     'h17
    [1075]    integral        8     'h2f
    [1076]    integral        8     'h88
  crc         integral        32    'h0
--------------------------------------------------

```
