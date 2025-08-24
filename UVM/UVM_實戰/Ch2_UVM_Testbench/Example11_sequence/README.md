# xrun.log
發送 10 筆 transaction 流程如下:
1. Driver 向 sequencer 發送申請 transaction 並且驅動它
<img width="766" height="424" alt="image" src="https://github.com/user-attachments/assets/e7004b30-81ec-4529-9e16-4e2d32f42f81" />

2. input monitor 監測到該 transaction, 將該 transaction 傳給 reference model
<img width="850" height="336" alt="image" src="https://github.com/user-attachments/assets/2dd1ad1c-5a21-4178-a9e6-48122f9593d6" />

3. reference model 收到這裡就單純 copy 一份再傳給 scoreboard
<img width="846" height="337" alt="image" src="https://github.com/user-attachments/assets/ae3fa47b-8ce4-45c4-861a-d9745ccbc97d" />

4. output monitor 監測到 DUT 的輸出並將其傳給 scoreboard
<img width="846" height="332" alt="image" src="https://github.com/user-attachments/assets/1cb1af6c-7603-4494-8c13-050620fd2aa3" />

5. scoreboard 收到來自 model 的 tr 和 output monitor 的 tr, 去做比對 (比對成功)
<img width="881" height="340" alt="image" src="https://github.com/user-attachments/assets/af856f01-27e7-4ba8-8726-3bfa002731dc" />

PS: 這邊確實 10 比 tr 比對成功
```
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
UVM_INFO my_sequence.sv(19) @ 0: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 1
UVM_INFO my_driver.sv(80) @ 1100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @4901
  dmac                         integral        48    'hacc282559a2f
  smac                         integral        48    'hd6fd6ca21be6
  ether_type                   integral        16    'h4680
  pload                        da(integral)    273   -
    [0]                        integral        8     'hc2
    [1]                        integral        8     'h34
    [2]                        integral        8     'he1
    [3]                        integral        8     'hc2
    [4]                        integral        8     'h69
    ...                        ...             ...   ...
    [268]                      integral        8     'h71
    [269]                      integral        8     'h8b
    [270]                      integral        8     'h7c
    [271]                      integral        8     'h65
    [272]                      integral        8     'h1e
  crc                          integral        32    'h0
  begin_time                   time            64    1100000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 2500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 2700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 60500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 60500000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 2
UVM_INFO my_driver.sv(80) @ 60500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5016
  dmac                         integral        48    'h1b9cf293233f
  smac                         integral        48    'hf79c2eacfec4
  ether_type                   integral        16    'hf247
  pload                        da(integral)    1059  -
    [0]                        integral        8     'h86
    [1]                        integral        8     'h6b
    [2]                        integral        8     'h13
    [3]                        integral        8     'h26
    [4]                        integral        8     'h9
    ...                        ...             ...   ...
    [1054]                     integral        8     'h80
    [1055]                     integral        8     'h16
    [1056]                     integral        8     'h51
    [1057]                     integral        8     'h45
    [1058]                     integral        8     'h57
  crc                          integral        32    'h0
  begin_time                   time            64    60500000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 60700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4890
  dmac        integral        48    'hacc282559a2f
  smac        integral        48    'hd6fd6ca21be6
  ether_type  integral        16    'h4680
  pload       da(integral)    273   -
    [0]       integral        8     'hc2
    [1]       integral        8     'h34
    [2]       integral        8     'he1
    [3]       integral        8     'hc2
    [4]       integral        8     'h69
    ...       ...             ...   ...
    [268]     integral        8     'h71
    [269]     integral        8     'h8b
    [270]     integral        8     'h7c
    [271]     integral        8     'h65
    [272]     integral        8     'h1e
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 60700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4964
  dmac        integral        48    'hacc282559a2f
  smac        integral        48    'hd6fd6ca21be6
  ether_type  integral        16    'h4680
  pload       da(integral)    273   -
    [0]       integral        8     'hc2
    [1]       integral        8     'h34
    [2]       integral        8     'he1
    [3]       integral        8     'hc2
    [4]       integral        8     'h69
    ...       ...             ...   ...
    [268]     integral        8     'h71
    [269]     integral        8     'h8b
    [270]     integral        8     'h7c
    [271]     integral        8     'h65
    [272]     integral        8     'h1e
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 60900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4858
  dmac        integral        48    'hacc282559a2f
  smac        integral        48    'hd6fd6ca21be6
  ether_type  integral        16    'h4680
  pload       da(integral)    273   -
    [0]       integral        8     'hc2
    [1]       integral        8     'h34
    [2]       integral        8     'he1
    [3]       integral        8     'hc2
    [4]       integral        8     'h69
    ...       ...             ...   ...
    [268]     integral        8     'h71
    [269]     integral        8     'h8b
    [270]     integral        8     'h7c
    [271]     integral        8     'h65
    [272]     integral        8     'h1e
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 60900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4858
  dmac        integral        48    'hacc282559a2f
  smac        integral        48    'hd6fd6ca21be6
  ether_type  integral        16    'h4680
  pload       da(integral)    273   -
    [0]       integral        8     'hc2
    [1]       integral        8     'h34
    [2]       integral        8     'he1
    [3]       integral        8     'hc2
    [4]       integral        8     'h69
    ...       ...             ...   ...
    [268]     integral        8     'h71
    [269]     integral        8     'h8b
    [270]     integral        8     'h7c
    [271]     integral        8     'h65
    [272]     integral        8     'h1e
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 61900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 62100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 277100000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 277100000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 3
UVM_INFO my_driver.sv(80) @ 277100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5012
  dmac                         integral        48    'h54a4a27f2d7
  smac                         integral        48    'hc8477f5c8dfe
  ether_type                   integral        16    'h54a
  pload                        da(integral)    908   -
    [0]                        integral        8     'h49
    [1]                        integral        8     'h67
    [2]                        integral        8     'h3e
    [3]                        integral        8     'hc9
    [4]                        integral        8     'hbf
    ...                        ...             ...   ...
    [903]                      integral        8     'h15
    [904]                      integral        8     'h1f
    [905]                      integral        8     'hbc
    [906]                      integral        8     'h80
    [907]                      integral        8     'h48
  crc                          integral        32    'h0
  begin_time                   time            64    277100000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 277300000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4888
  dmac        integral        48    'h1b9cf293233f
  smac        integral        48    'hf79c2eacfec4
  ether_type  integral        16    'hf247
  pload       da(integral)    1059  -
    [0]       integral        8     'h86
    [1]       integral        8     'h6b
    [2]       integral        8     'h13
    [3]       integral        8     'h26
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [1054]    integral        8     'h80
    [1055]    integral        8     'h16
    [1056]    integral        8     'h51
    [1057]    integral        8     'h45
    [1058]    integral        8     'h57
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 277300000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4889
  dmac        integral        48    'h1b9cf293233f
  smac        integral        48    'hf79c2eacfec4
  ether_type  integral        16    'hf247
  pload       da(integral)    1059  -
    [0]       integral        8     'h86
    [1]       integral        8     'h6b
    [2]       integral        8     'h13
    [3]       integral        8     'h26
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [1054]    integral        8     'h80
    [1055]    integral        8     'h16
    [1056]    integral        8     'h51
    [1057]    integral        8     'h45
    [1058]    integral        8     'h57
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 277500000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4867
  dmac        integral        48    'h1b9cf293233f
  smac        integral        48    'hf79c2eacfec4
  ether_type  integral        16    'hf247
  pload       da(integral)    1059  -
    [0]       integral        8     'h86
    [1]       integral        8     'h6b
    [2]       integral        8     'h13
    [3]       integral        8     'h26
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [1054]    integral        8     'h80
    [1055]    integral        8     'h16
    [1056]    integral        8     'h51
    [1057]    integral        8     'h45
    [1058]    integral        8     'h57
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 277500000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4867
  dmac        integral        48    'h1b9cf293233f
  smac        integral        48    'hf79c2eacfec4
  ether_type  integral        16    'hf247
  pload       da(integral)    1059  -
    [0]       integral        8     'h86
    [1]       integral        8     'h6b
    [2]       integral        8     'h13
    [3]       integral        8     'h26
    [4]       integral        8     'h9
    ...       ...             ...   ...
    [1054]    integral        8     'h80
    [1055]    integral        8     'h16
    [1056]    integral        8     'h51
    [1057]    integral        8     'h45
    [1058]    integral        8     'h57
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 278500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 278700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 463500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 463500000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 4
UVM_INFO my_driver.sv(80) @ 463500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5016
  dmac                         integral        48    'ha4fb41dc9f59
  smac                         integral        48    'h757320e74a15
  ether_type                   integral        16    'h978c
  pload                        da(integral)    473   -
    [0]                        integral        8     'h4e
    [1]                        integral        8     'h92
    [2]                        integral        8     'h3a
    [3]                        integral        8     'h16
    [4]                        integral        8     'h2d
    ...                        ...             ...   ...
    [468]                      integral        8     'h5
    [469]                      integral        8     'hc6
    [470]                      integral        8     'h4a
    [471]                      integral        8     'h1f
    [472]                      integral        8     'hb1
  crc                          integral        32    'h0
  begin_time                   time            64    463500000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 463700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5000
  dmac        integral        48    'h54a4a27f2d7
  smac        integral        48    'hc8477f5c8dfe
  ether_type  integral        16    'h54a
  pload       da(integral)    908   -
    [0]       integral        8     'h49
    [1]       integral        8     'h67
    [2]       integral        8     'h3e
    [3]       integral        8     'hc9
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [903]     integral        8     'h15
    [904]     integral        8     'h1f
    [905]     integral        8     'hbc
    [906]     integral        8     'h80
    [907]     integral        8     'h48
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 463700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4891
  dmac        integral        48    'h54a4a27f2d7
  smac        integral        48    'hc8477f5c8dfe
  ether_type  integral        16    'h54a
  pload       da(integral)    908   -
    [0]       integral        8     'h49
    [1]       integral        8     'h67
    [2]       integral        8     'h3e
    [3]       integral        8     'hc9
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [903]     integral        8     'h15
    [904]     integral        8     'h1f
    [905]     integral        8     'hbc
    [906]     integral        8     'h80
    [907]     integral        8     'h48
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 463900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4997
  dmac        integral        48    'h54a4a27f2d7
  smac        integral        48    'hc8477f5c8dfe
  ether_type  integral        16    'h54a
  pload       da(integral)    908   -
    [0]       integral        8     'h49
    [1]       integral        8     'h67
    [2]       integral        8     'h3e
    [3]       integral        8     'hc9
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [903]     integral        8     'h15
    [904]     integral        8     'h1f
    [905]     integral        8     'hbc
    [906]     integral        8     'h80
    [907]     integral        8     'h48
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 463900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4997
  dmac        integral        48    'h54a4a27f2d7
  smac        integral        48    'hc8477f5c8dfe
  ether_type  integral        16    'h54a
  pload       da(integral)    908   -
    [0]       integral        8     'h49
    [1]       integral        8     'h67
    [2]       integral        8     'h3e
    [3]       integral        8     'hc9
    [4]       integral        8     'hbf
    ...       ...             ...   ...
    [903]     integral        8     'h15
    [904]     integral        8     'h1f
    [905]     integral        8     'hbc
    [906]     integral        8     'h80
    [907]     integral        8     'h48
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 464900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 465100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 562900000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 562900000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 5
UVM_INFO my_driver.sv(80) @ 562900000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5012
  dmac                         integral        48    'h5e2271121fef
  smac                         integral        48    'h826b6623a1cb
  ether_type                   integral        16    'h5e5d
  pload                        da(integral)    219   -
    [0]                        integral        8     'h4a
    [1]                        integral        8     'h91
    [2]                        integral        8     'ha0
    [3]                        integral        8     'h96
    [4]                        integral        8     'h80
    ...                        ...             ...   ...
    [214]                      integral        8     'h97
    [215]                      integral        8     'h13
    [216]                      integral        8     'hf1
    [217]                      integral        8     'h6f
    [218]                      integral        8     'hee
  crc                          integral        32    'h0
  begin_time                   time            64    562900000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 563100000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4960
  dmac        integral        48    'ha4fb41dc9f59
  smac        integral        48    'h757320e74a15
  ether_type  integral        16    'h978c
  pload       da(integral)    473   -
    [0]       integral        8     'h4e
    [1]       integral        8     'h92
    [2]       integral        8     'h3a
    [3]       integral        8     'h16
    [4]       integral        8     'h2d
    ...       ...             ...   ...
    [468]     integral        8     'h5
    [469]     integral        8     'hc6
    [470]     integral        8     'h4a
    [471]     integral        8     'h1f
    [472]     integral        8     'hb1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 563100000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4971
  dmac        integral        48    'ha4fb41dc9f59
  smac        integral        48    'h757320e74a15
  ether_type  integral        16    'h978c
  pload       da(integral)    473   -
    [0]       integral        8     'h4e
    [1]       integral        8     'h92
    [2]       integral        8     'h3a
    [3]       integral        8     'h16
    [4]       integral        8     'h2d
    ...       ...             ...   ...
    [468]     integral        8     'h5
    [469]     integral        8     'hc6
    [470]     integral        8     'h4a
    [471]     integral        8     'h1f
    [472]     integral        8     'hb1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 563300000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4890
  dmac        integral        48    'ha4fb41dc9f59
  smac        integral        48    'h757320e74a15
  ether_type  integral        16    'h978c
  pload       da(integral)    473   -
    [0]       integral        8     'h4e
    [1]       integral        8     'h92
    [2]       integral        8     'h3a
    [3]       integral        8     'h16
    [4]       integral        8     'h2d
    ...       ...             ...   ...
    [468]     integral        8     'h5
    [469]     integral        8     'hc6
    [470]     integral        8     'h4a
    [471]     integral        8     'h1f
    [472]     integral        8     'hb1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 563300000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4890
  dmac        integral        48    'ha4fb41dc9f59
  smac        integral        48    'h757320e74a15
  ether_type  integral        16    'h978c
  pload       da(integral)    473   -
    [0]       integral        8     'h4e
    [1]       integral        8     'h92
    [2]       integral        8     'h3a
    [3]       integral        8     'h16
    [4]       integral        8     'h2d
    ...       ...             ...   ...
    [468]     integral        8     'h5
    [469]     integral        8     'hc6
    [470]     integral        8     'h4a
    [471]     integral        8     'h1f
    [472]     integral        8     'hb1
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 564300000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 564500000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 611500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 611500000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 6
UVM_INFO my_driver.sv(80) @ 611500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5016
  dmac                         integral        48    'h2706f207f711
  smac                         integral        48    'hb4fd78a21a42
  ether_type                   integral        16    'hd1c6
  pload                        da(integral)    146   -
    [0]                        integral        8     'hcf
    [1]                        integral        8     'h94
    [2]                        integral        8     'hd
    [3]                        integral        8     'he0
    [4]                        integral        8     'h9f
    ...                        ...             ...   ...
    [141]                      integral        8     'hd4
    [142]                      integral        8     'hab
    [143]                      integral        8     'hce
    [144]                      integral        8     'h86
    [145]                      integral        8     'h9c
  crc                          integral        32    'h0
  begin_time                   time            64    611500000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 611700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4949
  dmac        integral        48    'h5e2271121fef
  smac        integral        48    'h826b6623a1cb
  ether_type  integral        16    'h5e5d
  pload       da(integral)    219   -
    [0]       integral        8     'h4a
    [1]       integral        8     'h91
    [2]       integral        8     'ha0
    [3]       integral        8     'h96
    [4]       integral        8     'h80
    ...       ...             ...   ...
    [214]     integral        8     'h97
    [215]     integral        8     'h13
    [216]     integral        8     'hf1
    [217]     integral        8     'h6f
    [218]     integral        8     'hee
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 611700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4939
  dmac        integral        48    'h5e2271121fef
  smac        integral        48    'h826b6623a1cb
  ether_type  integral        16    'h5e5d
  pload       da(integral)    219   -
    [0]       integral        8     'h4a
    [1]       integral        8     'h91
    [2]       integral        8     'ha0
    [3]       integral        8     'h96
    [4]       integral        8     'h80
    ...       ...             ...   ...
    [214]     integral        8     'h97
    [215]     integral        8     'h13
    [216]     integral        8     'hf1
    [217]     integral        8     'h6f
    [218]     integral        8     'hee
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 611900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4888
  dmac        integral        48    'h5e2271121fef
  smac        integral        48    'h826b6623a1cb
  ether_type  integral        16    'h5e5d
  pload       da(integral)    219   -
    [0]       integral        8     'h4a
    [1]       integral        8     'h91
    [2]       integral        8     'ha0
    [3]       integral        8     'h96
    [4]       integral        8     'h80
    ...       ...             ...   ...
    [214]     integral        8     'h97
    [215]     integral        8     'h13
    [216]     integral        8     'hf1
    [217]     integral        8     'h6f
    [218]     integral        8     'hee
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 611900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4888
  dmac        integral        48    'h5e2271121fef
  smac        integral        48    'h826b6623a1cb
  ether_type  integral        16    'h5e5d
  pload       da(integral)    219   -
    [0]       integral        8     'h4a
    [1]       integral        8     'h91
    [2]       integral        8     'ha0
    [3]       integral        8     'h96
    [4]       integral        8     'h80
    ...       ...             ...   ...
    [214]     integral        8     'h97
    [215]     integral        8     'h13
    [216]     integral        8     'hf1
    [217]     integral        8     'h6f
    [218]     integral        8     'hee
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 612900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 613100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 645500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 645500000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 7
UVM_INFO my_driver.sv(80) @ 645500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5012
  dmac                         integral        48    'h962aa7ea248
  smac                         integral        48    'h475a2ed22e59
  ether_type                   integral        16    'h79bd
  pload                        da(integral)    254   -
    [0]                        integral        8     'h4b
    [1]                        integral        8     'h6c
    [2]                        integral        8     'he5
    [3]                        integral        8     'h5c
    [4]                        integral        8     'ha3
    ...                        ...             ...   ...
    [249]                      integral        8     'h64
    [250]                      integral        8     'h62
    [251]                      integral        8     'h8d
    [252]                      integral        8     'h98
    [253]                      integral        8     'hda
  crc                          integral        32    'h0
  begin_time                   time            64    645500000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 645700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4943
  dmac        integral        48    'h2706f207f711
  smac        integral        48    'hb4fd78a21a42
  ether_type  integral        16    'hd1c6
  pload       da(integral)    146   -
    [0]       integral        8     'hcf
    [1]       integral        8     'h94
    [2]       integral        8     'hd
    [3]       integral        8     'he0
    [4]       integral        8     'h9f
    ...       ...             ...   ...
    [141]     integral        8     'hd4
    [142]     integral        8     'hab
    [143]     integral        8     'hce
    [144]     integral        8     'h86
    [145]     integral        8     'h9c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 645700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4978
  dmac        integral        48    'h2706f207f711
  smac        integral        48    'hb4fd78a21a42
  ether_type  integral        16    'hd1c6
  pload       da(integral)    146   -
    [0]       integral        8     'hcf
    [1]       integral        8     'h94
    [2]       integral        8     'hd
    [3]       integral        8     'he0
    [4]       integral        8     'h9f
    ...       ...             ...   ...
    [141]     integral        8     'hd4
    [142]     integral        8     'hab
    [143]     integral        8     'hce
    [144]     integral        8     'h86
    [145]     integral        8     'h9c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 645900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5000
  dmac        integral        48    'h2706f207f711
  smac        integral        48    'hb4fd78a21a42
  ether_type  integral        16    'hd1c6
  pload       da(integral)    146   -
    [0]       integral        8     'hcf
    [1]       integral        8     'h94
    [2]       integral        8     'hd
    [3]       integral        8     'he0
    [4]       integral        8     'h9f
    ...       ...             ...   ...
    [141]     integral        8     'hd4
    [142]     integral        8     'hab
    [143]     integral        8     'hce
    [144]     integral        8     'h86
    [145]     integral        8     'h9c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 645900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5000
  dmac        integral        48    'h2706f207f711
  smac        integral        48    'hb4fd78a21a42
  ether_type  integral        16    'hd1c6
  pload       da(integral)    146   -
    [0]       integral        8     'hcf
    [1]       integral        8     'h94
    [2]       integral        8     'hd
    [3]       integral        8     'he0
    [4]       integral        8     'h9f
    ...       ...             ...   ...
    [141]     integral        8     'hd4
    [142]     integral        8     'hab
    [143]     integral        8     'hce
    [144]     integral        8     'h86
    [145]     integral        8     'h9c
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 646900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 647100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 701100000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 701100000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 8
UVM_INFO my_driver.sv(80) @ 701100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5016
  dmac                         integral        48    'h4205599d1766
  smac                         integral        48    'hf845af6df59c
  ether_type                   integral        16    'hd023
  pload                        da(integral)    544   -
    [0]                        integral        8     'h7a
    [1]                        integral        8     'h52
    [2]                        integral        8     'h43
    [3]                        integral        8     'h1
    [4]                        integral        8     'hba
    ...                        ...             ...   ...
    [539]                      integral        8     'hf5
    [540]                      integral        8     'h64
    [541]                      integral        8     'hab
    [542]                      integral        8     'he6
    [543]                      integral        8     'hd7
  crc                          integral        32    'h0
  begin_time                   time            64    701100000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 701300000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4937
  dmac        integral        48    'h962aa7ea248
  smac        integral        48    'h475a2ed22e59
  ether_type  integral        16    'h79bd
  pload       da(integral)    254   -
    [0]       integral        8     'h4b
    [1]       integral        8     'h6c
    [2]       integral        8     'he5
    [3]       integral        8     'h5c
    [4]       integral        8     'ha3
    ...       ...             ...   ...
    [249]     integral        8     'h64
    [250]     integral        8     'h62
    [251]     integral        8     'h8d
    [252]     integral        8     'h98
    [253]     integral        8     'hda
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 701300000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4961
  dmac        integral        48    'h962aa7ea248
  smac        integral        48    'h475a2ed22e59
  ether_type  integral        16    'h79bd
  pload       da(integral)    254   -
    [0]       integral        8     'h4b
    [1]       integral        8     'h6c
    [2]       integral        8     'he5
    [3]       integral        8     'h5c
    [4]       integral        8     'ha3
    ...       ...             ...   ...
    [249]     integral        8     'h64
    [250]     integral        8     'h62
    [251]     integral        8     'h8d
    [252]     integral        8     'h98
    [253]     integral        8     'hda
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 701500000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4960
  dmac        integral        48    'h962aa7ea248
  smac        integral        48    'h475a2ed22e59
  ether_type  integral        16    'h79bd
  pload       da(integral)    254   -
    [0]       integral        8     'h4b
    [1]       integral        8     'h6c
    [2]       integral        8     'he5
    [3]       integral        8     'h5c
    [4]       integral        8     'ha3
    ...       ...             ...   ...
    [249]     integral        8     'h64
    [250]     integral        8     'h62
    [251]     integral        8     'h8d
    [252]     integral        8     'h98
    [253]     integral        8     'hda
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 701500000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4960
  dmac        integral        48    'h962aa7ea248
  smac        integral        48    'h475a2ed22e59
  ether_type  integral        16    'h79bd
  pload       da(integral)    254   -
    [0]       integral        8     'h4b
    [1]       integral        8     'h6c
    [2]       integral        8     'he5
    [3]       integral        8     'h5c
    [4]       integral        8     'ha3
    ...       ...             ...   ...
    [249]     integral        8     'h64
    [250]     integral        8     'h62
    [251]     integral        8     'h8d
    [252]     integral        8     'h98
    [253]     integral        8     'hda
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 702500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 702700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 814700000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 814700000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 9
UVM_INFO my_driver.sv(80) @ 814700000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5012
  dmac                         integral        48    'h384da711623e
  smac                         integral        48    'h8cd9ef710695
  ether_type                   integral        16    'hab1e
  pload                        da(integral)    1015  -
    [0]                        integral        8     'had
    [1]                        integral        8     'h82
    [2]                        integral        8     'hcb
    [3]                        integral        8     'h3d
    [4]                        integral        8     'ha6
    ...                        ...             ...   ...
    [1010]                     integral        8     'hc2
    [1011]                     integral        8     'h2b
    [1012]                     integral        8     'haa
    [1013]                     integral        8     'h29
    [1014]                     integral        8     'h64
  crc                          integral        32    'h0
  begin_time                   time            64    814700000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 814900000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4957
  dmac        integral        48    'h4205599d1766
  smac        integral        48    'hf845af6df59c
  ether_type  integral        16    'hd023
  pload       da(integral)    544   -
    [0]       integral        8     'h7a
    [1]       integral        8     'h52
    [2]       integral        8     'h43
    [3]       integral        8     'h1
    [4]       integral        8     'hba
    ...       ...             ...   ...
    [539]     integral        8     'hf5
    [540]     integral        8     'h64
    [541]     integral        8     'hab
    [542]     integral        8     'he6
    [543]     integral        8     'hd7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 814900000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5041
  dmac        integral        48    'h4205599d1766
  smac        integral        48    'hf845af6df59c
  ether_type  integral        16    'hd023
  pload       da(integral)    544   -
    [0]       integral        8     'h7a
    [1]       integral        8     'h52
    [2]       integral        8     'h43
    [3]       integral        8     'h1
    [4]       integral        8     'hba
    ...       ...             ...   ...
    [539]     integral        8     'hf5
    [540]     integral        8     'h64
    [541]     integral        8     'hab
    [542]     integral        8     'he6
    [543]     integral        8     'hd7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 815100000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4949
  dmac        integral        48    'h4205599d1766
  smac        integral        48    'hf845af6df59c
  ether_type  integral        16    'hd023
  pload       da(integral)    544   -
    [0]       integral        8     'h7a
    [1]       integral        8     'h52
    [2]       integral        8     'h43
    [3]       integral        8     'h1
    [4]       integral        8     'hba
    ...       ...             ...   ...
    [539]     integral        8     'hf5
    [540]     integral        8     'h64
    [541]     integral        8     'hab
    [542]     integral        8     'he6
    [543]     integral        8     'hd7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 815100000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4949
  dmac        integral        48    'h4205599d1766
  smac        integral        48    'hf845af6df59c
  ether_type  integral        16    'hd023
  pload       da(integral)    544   -
    [0]       integral        8     'h7a
    [1]       integral        8     'h52
    [2]       integral        8     'h43
    [3]       integral        8     'h1
    [4]       integral        8     'hba
    ...       ...             ...   ...
    [539]     integral        8     'hf5
    [540]     integral        8     'h64
    [541]     integral        8     'hab
    [542]     integral        8     'he6
    [543]     integral        8     'hd7
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 816100000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 816300000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 1022500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_sequence.sv(19) @ 1022500000: uvm_test_top.i_agt.sqr@@seq [my_sequence] transaction: 10
UVM_INFO my_driver.sv(80) @ 1022500000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
-------------------------------------------------------------------------------
Name                           Type            Size  Value
-------------------------------------------------------------------------------
m_trans                        my_transaction  -     @5016
  dmac                         integral        48    'hb32dfb38480d
  smac                         integral        48    'hbaa7c366813a
  ether_type                   integral        16    'ha8d6
  pload                        da(integral)    317   -
    [0]                        integral        8     'h85
    [1]                        integral        8     'hbc
    [2]                        integral        8     'hac
    [3]                        integral        8     'h77
    [4]                        integral        8     'h31
    ...                        ...             ...   ...
    [312]                      integral        8     'h4
    [313]                      integral        8     'hfa
    [314]                      integral        8     'h30
    [315]                      integral        8     'hac
    [316]                      integral        8     'h8d
  crc                          integral        32    'h0
  begin_time                   time            64    1022500000
  depth                        int             32    'd2
  parent sequence (name)       string          3     seq
  parent sequence (full name)  string          26    uvm_test_top.i_agt.sqr.seq
  sequencer                    string          22    uvm_test_top.i_agt.sqr
-------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1022700000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4973
  dmac        integral        48    'h384da711623e
  smac        integral        48    'h8cd9ef710695
  ether_type  integral        16    'hab1e
  pload       da(integral)    1015  -
    [0]       integral        8     'had
    [1]       integral        8     'h82
    [2]       integral        8     'hcb
    [3]       integral        8     'h3d
    [4]       integral        8     'ha6
    ...       ...             ...   ...
    [1010]    integral        8     'hc2
    [1011]    integral        8     'h2b
    [1012]    integral        8     'haa
    [1013]    integral        8     'h29
    [1014]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 1022700000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5009
  dmac        integral        48    'h384da711623e
  smac        integral        48    'h8cd9ef710695
  ether_type  integral        16    'hab1e
  pload       da(integral)    1015  -
    [0]       integral        8     'had
    [1]       integral        8     'h82
    [2]       integral        8     'hcb
    [3]       integral        8     'h3d
    [4]       integral        8     'ha6
    ...       ...             ...   ...
    [1010]    integral        8     'hc2
    [1011]    integral        8     'h2b
    [1012]    integral        8     'haa
    [1013]    integral        8     'h29
    [1014]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1022900000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4943
  dmac        integral        48    'h384da711623e
  smac        integral        48    'h8cd9ef710695
  ether_type  integral        16    'hab1e
  pload       da(integral)    1015  -
    [0]       integral        8     'had
    [1]       integral        8     'h82
    [2]       integral        8     'hcb
    [3]       integral        8     'h3d
    [4]       integral        8     'ha6
    ...       ...             ...   ...
    [1010]    integral        8     'hc2
    [1011]    integral        8     'h2b
    [1012]    integral        8     'haa
    [1013]    integral        8     'h29
    [1014]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 1022900000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4943
  dmac        integral        48    'h384da711623e
  smac        integral        48    'h8cd9ef710695
  ether_type  integral        16    'hab1e
  pload       da(integral)    1015  -
    [0]       integral        8     'had
    [1]       integral        8     'h82
    [2]       integral        8     'hcb
    [3]       integral        8     'h3d
    [4]       integral        8     'ha6
    ...       ...             ...   ...
    [1010]    integral        8     'hc2
    [1011]    integral        8     'h2b
    [1012]    integral        8     'haa
    [1013]    integral        8     'h29
    [1014]    integral        8     'h64
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 1023900000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1024100000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(91) @ 1090700000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(63) @ 1090900000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5051
  dmac        integral        48    'hb32dfb38480d
  smac        integral        48    'hbaa7c366813a
  ether_type  integral        16    'ha8d6
  pload       da(integral)    317   -
    [0]       integral        8     'h85
    [1]       integral        8     'hbc
    [2]       integral        8     'hac
    [3]       integral        8     'h77
    [4]       integral        8     'h31
    ...       ...             ...   ...
    [312]     integral        8     'h4
    [313]     integral        8     'hfa
    [314]     integral        8     'h30
    [315]     integral        8     'hac
    [316]     integral        8     'h8d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 1090900000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @5054
  dmac        integral        48    'hb32dfb38480d
  smac        integral        48    'hbaa7c366813a
  ether_type  integral        16    'ha8d6
  pload       da(integral)    317   -
    [0]       integral        8     'h85
    [1]       integral        8     'hbc
    [2]       integral        8     'hac
    [3]       integral        8     'h77
    [4]       integral        8     'h31
    ...       ...             ...   ...
    [312]     integral        8     'h4
    [313]     integral        8     'hfa
    [314]     integral        8     'h30
    [315]     integral        8     'hac
    [316]     integral        8     'h8d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 1091100000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4937
  dmac        integral        48    'hb32dfb38480d
  smac        integral        48    'hbaa7c366813a
  ether_type  integral        16    'ha8d6
  pload       da(integral)    317   -
    [0]       integral        8     'h85
    [1]       integral        8     'hbc
    [2]       integral        8     'hac
    [3]       integral        8     'h77
    [4]       integral        8     'h31
    ...       ...             ...   ...
    [312]     integral        8     'h4
    [313]     integral        8     'hfa
    [314]     integral        8     'h30
    [315]     integral        8     'hac
    [316]     integral        8     'h8d
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 1091100000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4937
  dmac        integral        48    'hb32dfb38480d
  smac        integral        48    'hbaa7c366813a
  ether_type  integral        16    'ha8d6
  pload       da(integral)    317   -
    [0]       integral        8     'h85
    [1]       integral        8     'hbc
    [2]       integral        8     'hac
    [3]       integral        8     'h77
    [4]       integral        8     'h31
    ...       ...             ...   ...
    [312]     integral        8     'h4
    [313]     integral        8     'hfa
    [314]     integral        8     'h30
    [315]     integral        8     'hac
    [316]     integral        8     'h8d
  crc         integral        32    'h0
--------------------------------------------------
```
