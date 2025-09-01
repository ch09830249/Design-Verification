# command line
xrun -uvm -access +r ./tb/tlul_put_top.sv ./rtl/tlul_put_slave.sv -f ./tb/tlul_put_flist.f
# xrun.log
很明顯 mask 只有在 PutPartial 的時候才作用 (data_reg), PutFull 則依然後寫入完整 data
<img width="1565" height="569" alt="image" src="https://github.com/user-attachments/assets/fb09dc62-dff5-4eec-93c5-27844746240a" />

```
UVM_INFO @ 0: reporter [RNTST] Running test tlul_put_test...
UVM_INFO ./tb/agent/tlul_put_driver.sv(21) @ 20: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3660                               
  opcode                       integral          3     'h1                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'hc                                 
  address                      integral          32    'h79418e8d                          
  data                         integral          32    'h296ad6d4                          
  source                       integral          3     'h7                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    20                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(49) @ 35: uvm_test_top.env.agent.driver [tlul_put_driver] Sent TLUL PUT: addr=0x79418e8d data=0x296ad6d4 mask=0xc source=0x7
UVM_INFO ./tb/agent/tlul_put_monitor.sv(32) @ 35: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3782     
  opcode       integral          3     'h1       
  param        integral          3     'h0       
  size         integral          4     'h4       
  mask         integral          4     'hc       
  address      integral          32    'h79418e8d
  data         integral          32    'h296ad6d4
  source       integral          3     'h7       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(68) @ 55: uvm_test_top.env.agent.driver [tlul_put_driver] Received Response: opcode=0 data=0x00000000 source=0x7
UVM_INFO ./tb/agent/tlul_put_driver.sv(25) @ 55: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3660                               
  opcode                       integral          3     'h1                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'hc                                 
  address                      integral          32    'h79418e8d                          
  data                         integral          32    'h296ad6d4                          
  source                       integral          3     'h7                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h7                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    20                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_monitor.sv(45) @ 55: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3792
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h0  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h0  
  resp_data    integral          32    'h0  
  resp_source  integral          3     'h7  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(21) @ 55: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3755                               
  opcode                       integral          3     'h0                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'h3                                 
  address                      integral          32    'hdceb6e1                           
  data                         integral          32    'hc6d619a6                          
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    55                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_monitor.sv(32) @ 75: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3801     
  opcode       integral          3     'h0       
  param        integral          3     'h0       
  size         integral          4     'h4       
  mask         integral          4     'h3       
  address      integral          32    'hdceb6e1 
  data         integral          32    'hc6d619a6
  source       integral          3     'h4       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(49) @ 75: uvm_test_top.env.agent.driver [tlul_put_driver] Sent TLUL PUT: addr=0x0dceb6e1 data=0xc6d619a6 mask=0x3 source=0x4
UVM_INFO ./tb/agent/tlul_put_monitor.sv(45) @ 95: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3768
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h0  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h0  
  resp_data    integral          32    'h0  
  resp_source  integral          3     'h4  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(68) @ 95: uvm_test_top.env.agent.driver [tlul_put_driver] Received Response: opcode=0 data=0x00000000 source=0x4
UVM_INFO ./tb/agent/tlul_put_driver.sv(25) @ 95: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3755                               
  opcode                       integral          3     'h0                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'h3                                 
  address                      integral          32    'hdceb6e1                           
  data                         integral          32    'hc6d619a6                          
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h4                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    55                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(21) @ 95: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3730                               
  opcode                       integral          3     'h0                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'h1                                 
  address                      integral          32    'h3c7a4c39                          
  data                         integral          32    'h696032cd                          
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    95                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_monitor.sv(32) @ 115: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3802     
  opcode       integral          3     'h0       
  param        integral          3     'h0       
  size         integral          4     'h4       
  mask         integral          4     'h1       
  address      integral          32    'h3c7a4c39
  data         integral          32    'h696032cd
  source       integral          3     'h4       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(49) @ 115: uvm_test_top.env.agent.driver [tlul_put_driver] Sent TLUL PUT: addr=0x3c7a4c39 data=0x696032cd mask=0x1 source=0x4
UVM_INFO ./tb/agent/tlul_put_monitor.sv(45) @ 135: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3707
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h0  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h0  
  resp_data    integral          32    'h0  
  resp_source  integral          3     'h4  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(68) @ 135: uvm_test_top.env.agent.driver [tlul_put_driver] Received Response: opcode=0 data=0x00000000 source=0x4
UVM_INFO ./tb/agent/tlul_put_driver.sv(25) @ 135: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3730                               
  opcode                       integral          3     'h0                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'h1                                 
  address                      integral          32    'h3c7a4c39                          
  data                         integral          32    'h696032cd                          
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h4                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    95                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(21) @ 135: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3669                               
  opcode                       integral          3     'h1                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'hf                                 
  address                      integral          32    'h65ee8a5c                          
  data                         integral          32    'h1d95cce1                          
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    135                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_monitor.sv(32) @ 155: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3803     
  opcode       integral          3     'h1       
  param        integral          3     'h0       
  size         integral          4     'h4       
  mask         integral          4     'hf       
  address      integral          32    'h65ee8a5c
  data         integral          32    'h1d95cce1
  source       integral          3     'h4       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(49) @ 155: uvm_test_top.env.agent.driver [tlul_put_driver] Sent TLUL PUT: addr=0x65ee8a5c data=0x1d95cce1 mask=0xf source=0x4
UVM_INFO ./tb/agent/tlul_put_monitor.sv(45) @ 175: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3795
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h0  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h0  
  resp_data    integral          32    'h0  
  resp_source  integral          3     'h4  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(68) @ 175: uvm_test_top.env.agent.driver [tlul_put_driver] Received Response: opcode=0 data=0x00000000 source=0x4
UVM_INFO ./tb/agent/tlul_put_driver.sv(25) @ 175: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3669                               
  opcode                       integral          3     'h1                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'hf                                 
  address                      integral          32    'h65ee8a5c                          
  data                         integral          32    'h1d95cce1                          
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h4                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    135                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(21) @ 175: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3731                               
  opcode                       integral          3     'h1                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'h3                                 
  address                      integral          32    'hfbe294dd                          
  data                         integral          32    'heb7f3946                          
  source                       integral          3     'h5                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    175                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_monitor.sv(32) @ 195: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3804     
  opcode       integral          3     'h1       
  param        integral          3     'h0       
  size         integral          4     'h4       
  mask         integral          4     'h3       
  address      integral          32    'hfbe294dd
  data         integral          32    'heb7f3946
  source       integral          3     'h5       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(49) @ 195: uvm_test_top.env.agent.driver [tlul_put_driver] Sent TLUL PUT: addr=0xfbe294dd data=0xeb7f3946 mask=0x3 source=0x5
UVM_INFO ./tb/agent/tlul_put_monitor.sv(45) @ 215: uvm_test_top.env.agent.monitor [tlul_put_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3800
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h0  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h0  
  resp_data    integral          32    'h0  
  resp_source  integral          3     'h5  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_put_driver.sv(68) @ 215: uvm_test_top.env.agent.driver [tlul_put_driver] Received Response: opcode=0 data=0x00000000 source=0x5
UVM_INFO ./tb/agent/tlul_put_driver.sv(25) @ 215: uvm_test_top.env.agent.driver [tlul_put_driver] before put
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3731                               
  opcode                       integral          3     'h1                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h4                                 
  mask                         integral          4     'h3                                 
  address                      integral          32    'hfbe294dd                          
  data                         integral          32    'heb7f3946                          
  source                       integral          3     'h5                                 
  is_get                       integral          1     'h0                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h5                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    175                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 215: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```
