# command line
xrun -uvm -access +r ./tb/tlul_get_top.sv ./rtl/tlul_get_slave.sv -f ./tb/tlul_get_flist.f
# xrun.log
<img width="1857" height="642" alt="image" src="https://github.com/user-attachments/assets/8498c65c-d623-4c37-9f30-421154df65e9" />

```
UVM_INFO @ 0: reporter [RNTST] Running test tlul_get_test...
UVM_INFO ./tb/agent/tlul_get_driver.sv(21) @ 20: uvm_test_top.env.agent.driver [tlul_get_driver] before get
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3660                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h1                                 
  address                      integral          32    'hd8dfe655                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h1                                 
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
UVM_INFO ./tb/agent/tlul_get_monitor.sv(32) @ 25: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3760     
  opcode       integral          3     'h4       
  param        integral          3     'h0       
  size         integral          4     'h2       
  mask         integral          4     'h1       
  address      integral          32    'hd8dfe655
  data         integral          32    'h0       
  source       integral          3     'h4       
  is_get       integral          1     'h1       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(57) @ 45: uvm_test_top.env.agent.driver [tlul_get_driver] after read
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3660                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h1                                 
  address                      integral          32    'hd8dfe655                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h4                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h4                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h4                                 
  resp_data                    integral          32    'h4f                                
  resp_source                  integral          3     'h4                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    20                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(45) @ 45: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3790
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h4  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h4  
  resp_data    integral          32    'h4f 
  resp_source  integral          3     'h4  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(21) @ 45: uvm_test_top.env.agent.driver [tlul_get_driver] before get
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3719                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h0                                 
  address                      integral          32    'h36867f7a                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h6                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    45                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(32) @ 55: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3798     
  opcode       integral          3     'h4       
  param        integral          3     'h0       
  size         integral          4     'h2       
  mask         integral          4     'h0       
  address      integral          32    'h36867f7a
  data         integral          32    'h0       
  source       integral          3     'h6       
  is_get       integral          1     'h1       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(45) @ 75: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3767
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h4  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h4  
  resp_data    integral          32    'h0  
  resp_source  integral          3     'h6  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(57) @ 75: uvm_test_top.env.agent.driver [tlul_get_driver] after read
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3719                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h0                                 
  address                      integral          32    'h36867f7a                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h6                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h4                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h4                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h6                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    45                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(21) @ 75: uvm_test_top.env.agent.driver [tlul_get_driver] before get
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3726                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'he                                 
  address                      integral          32    'hfaa622eb                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h5                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    75                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(32) @ 85: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3716     
  opcode       integral          3     'h4       
  param        integral          3     'h0       
  size         integral          4     'h2       
  mask         integral          4     'he       
  address      integral          32    'hfaa622eb
  data         integral          32    'h0       
  source       integral          3     'h5       
  is_get       integral          1     'h1       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(45) @ 105: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record D channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3743     
  opcode       integral          3     'h0       
  param        integral          3     'h0       
  size         integral          4     'h0       
  mask         integral          4     'h0       
  address      integral          32    'h0       
  data         integral          32    'h0       
  source       integral          3     'h0       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h4       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h4       
  resp_data    integral          32    'h1a2b3c00
  resp_source  integral          3     'h5       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(57) @ 105: uvm_test_top.env.agent.driver [tlul_get_driver] after read
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3726                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'he                                 
  address                      integral          32    'hfaa622eb                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h5                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h4                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h4                                 
  resp_data                    integral          32    'h1a2b3c00                          
  resp_source                  integral          3     'h5                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    75                                  
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(21) @ 105: uvm_test_top.env.agent.driver [tlul_get_driver] before get
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3669                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h1                                 
  address                      integral          32    'h67892418                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h1                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h0                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h0                                 
  resp_data                    integral          32    'h0                                 
  resp_source                  integral          3     'h0                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    105                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(32) @ 115: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3766     
  opcode       integral          3     'h4       
  param        integral          3     'h0       
  size         integral          4     'h2       
  mask         integral          4     'h1       
  address      integral          32    'h67892418
  data         integral          32    'h0       
  source       integral          3     'h1       
  is_get       integral          1     'h1       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(45) @ 135: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record D channel
--------------------------------------------
Name           Type              Size  Value
--------------------------------------------
tr             tlul_transaction  -     @3740
  opcode       integral          3     'h0  
  param        integral          3     'h0  
  size         integral          4     'h0  
  mask         integral          4     'h0  
  address      integral          32    'h0  
  data         integral          32    'h0  
  source       integral          3     'h0  
  is_get       integral          1     'h0  
  resp_opcode  integral          3     'h4  
  resp_param   integral          3     'h0  
  resp_size    integral          4     'h4  
  resp_data    integral          32    'h4f 
  resp_source  integral          3     'h1  
  resp_sink    integral          2     'h0  
--------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(57) @ 135: uvm_test_top.env.agent.driver [tlul_get_driver] after read
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3669                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h1                                 
  address                      integral          32    'h67892418                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h1                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h4                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h4                                 
  resp_data                    integral          32    'h4f                                
  resp_source                  integral          3     'h1                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    105                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(21) @ 135: uvm_test_top.env.agent.driver [tlul_get_driver] before get
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3735                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h9                                 
  address                      integral          32    'h6b1e07de                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h6                                 
  is_get                       integral          1     'h1                                 
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
UVM_INFO ./tb/agent/tlul_get_monitor.sv(32) @ 145: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record A channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3776     
  opcode       integral          3     'h4       
  param        integral          3     'h0       
  size         integral          4     'h2       
  mask         integral          4     'h9       
  address      integral          32    'h6b1e07de
  data         integral          32    'h0       
  source       integral          3     'h6       
  is_get       integral          1     'h1       
  resp_opcode  integral          3     'h0       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h0       
  resp_data    integral          32    'h0       
  resp_source  integral          3     'h0       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_monitor.sv(45) @ 165: uvm_test_top.env.agent.monitor [tlul_get_monitor] Record D channel
-------------------------------------------------
Name           Type              Size  Value     
-------------------------------------------------
tr             tlul_transaction  -     @3736     
  opcode       integral          3     'h0       
  param        integral          3     'h0       
  size         integral          4     'h0       
  mask         integral          4     'h0       
  address      integral          32    'h0       
  data         integral          32    'h0       
  source       integral          3     'h0       
  is_get       integral          1     'h0       
  resp_opcode  integral          3     'h4       
  resp_param   integral          3     'h0       
  resp_size    integral          4     'h4       
  resp_data    integral          32    'h1a00004f
  resp_source  integral          3     'h6       
  resp_sink    integral          2     'h0       
-------------------------------------------------
UVM_INFO ./tb/agent/tlul_get_driver.sv(57) @ 165: uvm_test_top.env.agent.driver [tlul_get_driver] after read
-------------------------------------------------------------------------------------------
Name                           Type              Size  Value                               
-------------------------------------------------------------------------------------------
tr                             tlul_transaction  -     @3735                               
  opcode                       integral          3     'h4                                 
  param                        integral          3     'h0                                 
  size                         integral          4     'h2                                 
  mask                         integral          4     'h9                                 
  address                      integral          32    'h6b1e07de                          
  data                         integral          32    'h0                                 
  source                       integral          3     'h6                                 
  is_get                       integral          1     'h1                                 
  resp_opcode                  integral          3     'h4                                 
  resp_param                   integral          3     'h0                                 
  resp_size                    integral          4     'h4                                 
  resp_data                    integral          32    'h1a00004f                          
  resp_source                  integral          3     'h6                                 
  resp_sink                    integral          2     'h0                                 
  begin_time                   time              64    135                                 
  depth                        int               32    'd2                                 
  parent sequence (name)       string            3     seq                                 
  parent sequence (full name)  string            36    uvm_test_top.env.agent.sequencer.seq
  sequencer                    string            32    uvm_test_top.env.agent.sequencer    
-------------------------------------------------------------------------------------------
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 165: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```
