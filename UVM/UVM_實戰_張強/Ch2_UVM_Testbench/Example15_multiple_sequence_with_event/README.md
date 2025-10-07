# xrun.log
1. 確實 long payload transaction 先發送
<img width="1455" height="396" alt="image" src="https://github.com/user-attachments/assets/265f4d81-4da8-422f-9983-38afa318a1ea" />  
<img width="1055" height="742" alt="image" src="https://github.com/user-attachments/assets/073de54c-ae1a-4ee0-a03a-234f8519ac12" />
<img width="1472" height="398" alt="image" src="https://github.com/user-attachments/assets/74c8461f-485c-44c5-baf2-2a3460041c36" />  
2. 後續兩個 port 各自 seq 發送 transaction
<img width="1486" height="382" alt="image" src="https://github.com/user-attachments/assets/a4a6205c-5e97-4636-b171-f3d54676d955" />
<img width="1060" height="652" alt="image" src="https://github.com/user-attachments/assets/a1c0a6b3-7e65-49e1-b575-c25c268ec373" />
<img width="1057" height="657" alt="image" src="https://github.com/user-attachments/assets/b4ed85a7-0229-40bb-8dc6-45e2c7385b59" />  

```
UVM_INFO my_case0.sv(61) @ 0: uvm_test_top [my_case0] my_case0 base test is new
UVM_INFO my_env.sv(16) @ 0: uvm_test_top.env0 [my_env] my_envs (env0) is new
UVM_INFO my_env.sv(16) @ 0: uvm_test_top.env1 [my_env] my_envs (env1) is new
UVM_INFO @ 0: reporter [RNTST] Running test my_case0...
UVM_INFO my_case0.sv(19) @ 0: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send the first long payload tran
UVM_INFO my_driver.sv(38) @ 1100000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7124                               
  dmac                         integral        48    'hffd9ba1e9c7b                      
  smac                         integral        48    'hfff31918900d                      
  ether_type                   integral        16    'h9b09                              
  pload                        da(integral)    25    -                                   
    [0]                        integral        8     'hf4                                
    [1]                        integral        8     'h91                                
    [2]                        integral        8     'hc4                                
    [3]                        integral        8     'ha5                                
    [4]                        integral        8     'h5                                 
    ...                        ...             ...   ...                                 
    [20]                       integral        8     'h1d                                
    [21]                       integral        8     'h26                                
    [22]                       integral        8     'hf4                                
    [23]                       integral        8     'hcc                                
    [24]                       integral        8     'h32                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    1100000                             
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 2500000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 2700000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 10900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(38) @ 10900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7238                               
  dmac                         integral        48    'h81ba73b8615e                      
  smac                         integral        48    'hffaa211d068a                      
  ether_type                   integral        16    'hc2d0                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h10                                
    [1]                        integral        8     'h16                                
    [2]                        integral        8     'h17                                
    [3]                        integral        8     'h2f                                
    [4]                        integral        8     'h56                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'h4a                                
    [17]                       integral        8     'h4a                                
    [18]                       integral        8     'hb7                                
    [19]                       integral        8     'hb5                                
    [20]                       integral        8     'h29                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    10900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_driver.sv(38) @ 10900000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7234                               
  dmac                         integral        48    'h8708436b2ff7                      
  smac                         integral        48    'hff9a8d6a323c                      
  ether_type                   integral        16    'hf212                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'hdd                                
    [1]                        integral        8     'h3d                                
    [2]                        integral        8     'h39                                
    [3]                        integral        8     'h5                                 
    [4]                        integral        8     'hb5                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h53                                
    [18]                       integral        8     'h5b                                
    [19]                       integral        8     'h87                                
    [20]                       integral        8     'h15                                
    [21]                       integral        8     'hcc                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    10900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 11100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7107         
  dmac        integral        48    'hffd9ba1e9c7b
  smac        integral        48    'hfff31918900d
  ether_type  integral        16    'h9b09        
  pload       da(integral)    25    -             
    [0]       integral        8     'hf4          
    [1]       integral        8     'h91          
    [2]       integral        8     'hc4          
    [3]       integral        8     'ha5          
    [4]       integral        8     'h5           
    ...       ...             ...   ...           
    [20]      integral        8     'h1d          
    [21]      integral        8     'h26          
    [22]      integral        8     'hf4          
    [23]      integral        8     'hcc          
    [24]      integral        8     'h32          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 11100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7159         
  dmac        integral        48    'hffd9ba1e9c7b
  smac        integral        48    'hfff31918900d
  ether_type  integral        16    'h9b09        
  pload       da(integral)    25    -             
    [0]       integral        8     'hf4          
    [1]       integral        8     'h91          
    [2]       integral        8     'hc4          
    [3]       integral        8     'ha5          
    [4]       integral        8     'h5           
    ...       ...             ...   ...           
    [20]      integral        8     'h1d          
    [21]      integral        8     'h26          
    [22]      integral        8     'hf4          
    [23]      integral        8     'hcc          
    [24]      integral        8     'h32          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 11300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7090         
  dmac        integral        48    'hffd9ba1e9c7b
  smac        integral        48    'hfff31918900d
  ether_type  integral        16    'h9b09        
  pload       da(integral)    25    -             
    [0]       integral        8     'hf4          
    [1]       integral        8     'h91          
    [2]       integral        8     'hc4          
    [3]       integral        8     'ha5          
    [4]       integral        8     'h5           
    ...       ...             ...   ...           
    [20]      integral        8     'h1d          
    [21]      integral        8     'h26          
    [22]      integral        8     'hf4          
    [23]      integral        8     'hcc          
    [24]      integral        8     'h32          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 11300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7090         
  dmac        integral        48    'hffd9ba1e9c7b
  smac        integral        48    'hfff31918900d
  ether_type  integral        16    'h9b09        
  pload       da(integral)    25    -             
    [0]       integral        8     'hf4          
    [1]       integral        8     'h91          
    [2]       integral        8     'hc4          
    [3]       integral        8     'ha5          
    [4]       integral        8     'h5           
    ...       ...             ...   ...           
    [20]      integral        8     'h1d          
    [21]      integral        8     'h26          
    [22]      integral        8     'hf4          
    [23]      integral        8     'hcc          
    [24]      integral        8     'h32          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 12300000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 12300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 12500000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 12500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 19900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 19900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 19900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7160                               
  dmac                         integral        48    'h64548e99f6f5                      
  smac                         integral        48    'h895efe24ff3                       
  ether_type                   integral        16    'h516f                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'he3                                
    [1]                        integral        8     'h68                                
    [2]                        integral        8     'h33                                
    [3]                        integral        8     'ha3                                
    [4]                        integral        8     'h7b                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'hc1                                
    [17]                       integral        8     'ha3                                
    [18]                       integral        8     'ha8                                
    [19]                       integral        8     'h24                                
    [20]                       integral        8     'hae                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    19900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_driver.sv(49) @ 20100000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(59) @ 20100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7114         
  dmac        integral        48    'h81ba73b8615e
  smac        integral        48    'hffaa211d068a
  ether_type  integral        16    'hc2d0        
  pload       da(integral)    21    -             
    [0]       integral        8     'h10          
    [1]       integral        8     'h16          
    [2]       integral        8     'h17          
    [3]       integral        8     'h2f          
    [4]       integral        8     'h56          
    ...       ...             ...   ...           
    [16]      integral        8     'h4a          
    [17]      integral        8     'h4a          
    [18]      integral        8     'hb7          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h29          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_case0.sv(46) @ 20100000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_model.sv(30) @ 20100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7113         
  dmac        integral        48    'h81ba73b8615e
  smac        integral        48    'hffaa211d068a
  ether_type  integral        16    'hc2d0        
  pload       da(integral)    21    -             
    [0]       integral        8     'h10          
    [1]       integral        8     'h16          
    [2]       integral        8     'h17          
    [3]       integral        8     'h2f          
    [4]       integral        8     'h56          
    ...       ...             ...   ...           
    [16]      integral        8     'h4a          
    [17]      integral        8     'h4a          
    [18]      integral        8     'hb7          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h29          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(38) @ 20100000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7151                               
  dmac                         integral        48    'h8816fd04f4da                      
  smac                         integral        48    'h284696fe56a1                      
  ether_type                   integral        16    'hd7eb                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'hf6                                
    [1]                        integral        8     'h3c                                
    [2]                        integral        8     'hd0                                
    [3]                        integral        8     'hb0                                
    [4]                        integral        8     'hd3                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h9d                                
    [18]                       integral        8     'h1a                                
    [19]                       integral        8     'hdb                                
    [20]                       integral        8     'h2e                                
    [21]                       integral        8     'h88                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    20100000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 20300000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7077         
  dmac        integral        48    'h8708436b2ff7
  smac        integral        48    'hff9a8d6a323c
  ether_type  integral        16    'hf212        
  pload       da(integral)    22    -             
    [0]       integral        8     'hdd          
    [1]       integral        8     'h3d          
    [2]       integral        8     'h39          
    [3]       integral        8     'h5           
    [4]       integral        8     'hb5          
    ...       ...             ...   ...           
    [17]      integral        8     'h53          
    [18]      integral        8     'h5b          
    [19]      integral        8     'h87          
    [20]      integral        8     'h15          
    [21]      integral        8     'hcc          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 20300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7092         
  dmac        integral        48    'h81ba73b8615e
  smac        integral        48    'hffaa211d068a
  ether_type  integral        16    'hc2d0        
  pload       da(integral)    21    -             
    [0]       integral        8     'h10          
    [1]       integral        8     'h16          
    [2]       integral        8     'h17          
    [3]       integral        8     'h2f          
    [4]       integral        8     'h56          
    ...       ...             ...   ...           
    [16]      integral        8     'h4a          
    [17]      integral        8     'h4a          
    [18]      integral        8     'hb7          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h29          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 20300000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7268         
  dmac        integral        48    'h8708436b2ff7
  smac        integral        48    'hff9a8d6a323c
  ether_type  integral        16    'hf212        
  pload       da(integral)    22    -             
    [0]       integral        8     'hdd          
    [1]       integral        8     'h3d          
    [2]       integral        8     'h39          
    [3]       integral        8     'h5           
    [4]       integral        8     'hb5          
    ...       ...             ...   ...           
    [17]      integral        8     'h53          
    [18]      integral        8     'h5b          
    [19]      integral        8     'h87          
    [20]      integral        8     'h15          
    [21]      integral        8     'hcc          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 20300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7092         
  dmac        integral        48    'h81ba73b8615e
  smac        integral        48    'hffaa211d068a
  ether_type  integral        16    'hc2d0        
  pload       da(integral)    21    -             
    [0]       integral        8     'h10          
    [1]       integral        8     'h16          
    [2]       integral        8     'h17          
    [3]       integral        8     'h2f          
    [4]       integral        8     'h56          
    ...       ...             ...   ...           
    [16]      integral        8     'h4a          
    [17]      integral        8     'h4a          
    [18]      integral        8     'hb7          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h29          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 20500000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7045         
  dmac        integral        48    'h8708436b2ff7
  smac        integral        48    'hff9a8d6a323c
  ether_type  integral        16    'hf212        
  pload       da(integral)    22    -             
    [0]       integral        8     'hdd          
    [1]       integral        8     'h3d          
    [2]       integral        8     'h39          
    [3]       integral        8     'h5           
    [4]       integral        8     'hb5          
    ...       ...             ...   ...           
    [17]      integral        8     'h53          
    [18]      integral        8     'h5b          
    [19]      integral        8     'h87          
    [20]      integral        8     'h15          
    [21]      integral        8     'hcc          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 20500000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7045         
  dmac        integral        48    'h8708436b2ff7
  smac        integral        48    'hff9a8d6a323c
  ether_type  integral        16    'hf212        
  pload       da(integral)    22    -             
    [0]       integral        8     'hdd          
    [1]       integral        8     'h3d          
    [2]       integral        8     'h39          
    [3]       integral        8     'h5           
    [4]       integral        8     'hb5          
    ...       ...             ...   ...           
    [17]      integral        8     'h53          
    [18]      integral        8     'h5b          
    [19]      integral        8     'h87          
    [20]      integral        8     'h15          
    [21]      integral        8     'hcc          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 21300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 21500000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 21500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 21700000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 28900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 28900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 28900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7230                               
  dmac                         integral        48    'h10d60ac35d42                      
  smac                         integral        48    'hc4ab5497efa3                      
  ether_type                   integral        16    'hfe9c                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h26                                
    [1]                        integral        8     'h6d                                
    [2]                        integral        8     'h5e                                
    [3]                        integral        8     'h9f                                
    [4]                        integral        8     'hc9                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'h3e                                
    [17]                       integral        8     'h6c                                
    [18]                       integral        8     'h4                                 
    [19]                       integral        8     'h8f                                
    [20]                       integral        8     'h5d                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    28900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 29100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7259         
  dmac        integral        48    'h64548e99f6f5
  smac        integral        48    'h895efe24ff3 
  ether_type  integral        16    'h516f        
  pload       da(integral)    21    -             
    [0]       integral        8     'he3          
    [1]       integral        8     'h68          
    [2]       integral        8     'h33          
    [3]       integral        8     'ha3          
    [4]       integral        8     'h7b          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'ha3          
    [18]      integral        8     'ha8          
    [19]      integral        8     'h24          
    [20]      integral        8     'hae          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 29100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7115         
  dmac        integral        48    'h64548e99f6f5
  smac        integral        48    'h895efe24ff3 
  ether_type  integral        16    'h516f        
  pload       da(integral)    21    -             
    [0]       integral        8     'he3          
    [1]       integral        8     'h68          
    [2]       integral        8     'h33          
    [3]       integral        8     'ha3          
    [4]       integral        8     'h7b          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'ha3          
    [18]      integral        8     'ha8          
    [19]      integral        8     'h24          
    [20]      integral        8     'hae          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 29300000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(59) @ 29300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7254         
  dmac        integral        48    'h64548e99f6f5
  smac        integral        48    'h895efe24ff3 
  ether_type  integral        16    'h516f        
  pload       da(integral)    21    -             
    [0]       integral        8     'he3          
    [1]       integral        8     'h68          
    [2]       integral        8     'h33          
    [3]       integral        8     'ha3          
    [4]       integral        8     'h7b          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'ha3          
    [18]      integral        8     'ha8          
    [19]      integral        8     'h24          
    [20]      integral        8     'hae          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_case0.sv(46) @ 29300000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_scoreboard.sv(39) @ 29300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7254         
  dmac        integral        48    'h64548e99f6f5
  smac        integral        48    'h895efe24ff3 
  ether_type  integral        16    'h516f        
  pload       da(integral)    21    -             
    [0]       integral        8     'he3          
    [1]       integral        8     'h68          
    [2]       integral        8     'h33          
    [3]       integral        8     'ha3          
    [4]       integral        8     'h7b          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'ha3          
    [18]      integral        8     'ha8          
    [19]      integral        8     'h24          
    [20]      integral        8     'hae          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(38) @ 29300000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7216                               
  dmac                         integral        48    'heb8317e68a71                      
  smac                         integral        48    'h83b6433f221                       
  ether_type                   integral        16    'ha879                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'hcd                                
    [1]                        integral        8     'h14                                
    [2]                        integral        8     'ha8                                
    [3]                        integral        8     'h4                                 
    [4]                        integral        8     'h2b                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h3c                                
    [18]                       integral        8     'h86                                
    [19]                       integral        8     'hea                                
    [20]                       integral        8     'ha5                                
    [21]                       integral        8     'h5a                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    29300000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 29500000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7085         
  dmac        integral        48    'h8816fd04f4da
  smac        integral        48    'h284696fe56a1
  ether_type  integral        16    'hd7eb        
  pload       da(integral)    22    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h3c          
    [2]       integral        8     'hd0          
    [3]       integral        8     'hb0          
    [4]       integral        8     'hd3          
    ...       ...             ...   ...           
    [17]      integral        8     'h9d          
    [18]      integral        8     'h1a          
    [19]      integral        8     'hdb          
    [20]      integral        8     'h2e          
    [21]      integral        8     'h88          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 29500000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7084         
  dmac        integral        48    'h8816fd04f4da
  smac        integral        48    'h284696fe56a1
  ether_type  integral        16    'hd7eb        
  pload       da(integral)    22    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h3c          
    [2]       integral        8     'hd0          
    [3]       integral        8     'hb0          
    [4]       integral        8     'hd3          
    ...       ...             ...   ...           
    [17]      integral        8     'h9d          
    [18]      integral        8     'h1a          
    [19]      integral        8     'hdb          
    [20]      integral        8     'h2e          
    [21]      integral        8     'h88          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 29700000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7061         
  dmac        integral        48    'h8816fd04f4da
  smac        integral        48    'h284696fe56a1
  ether_type  integral        16    'hd7eb        
  pload       da(integral)    22    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h3c          
    [2]       integral        8     'hd0          
    [3]       integral        8     'hb0          
    [4]       integral        8     'hd3          
    ...       ...             ...   ...           
    [17]      integral        8     'h9d          
    [18]      integral        8     'h1a          
    [19]      integral        8     'hdb          
    [20]      integral        8     'h2e          
    [21]      integral        8     'h88          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 29700000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7061         
  dmac        integral        48    'h8816fd04f4da
  smac        integral        48    'h284696fe56a1
  ether_type  integral        16    'hd7eb        
  pload       da(integral)    22    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h3c          
    [2]       integral        8     'hd0          
    [3]       integral        8     'hb0          
    [4]       integral        8     'hd3          
    ...       ...             ...   ...           
    [17]      integral        8     'h9d          
    [18]      integral        8     'h1a          
    [19]      integral        8     'hdb          
    [20]      integral        8     'h2e          
    [21]      integral        8     'h88          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 30300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 30500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 30700000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 30900000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 37900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 37900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 37900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7203                               
  dmac                         integral        48    'h916ce8349444                      
  smac                         integral        48    'h1c62e9fda8cb                      
  ether_type                   integral        16    'hb94                               
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'hf6                                
    [1]                        integral        8     'h69                                
    [2]                        integral        8     'h5d                                
    [3]                        integral        8     'h5                                 
    [4]                        integral        8     'h48                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'hc1                                
    [17]                       integral        8     'h67                                
    [18]                       integral        8     'hb9                                
    [19]                       integral        8     'hc7                                
    [20]                       integral        8     'hf1                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    37900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 38100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7182         
  dmac        integral        48    'h10d60ac35d42
  smac        integral        48    'hc4ab5497efa3
  ether_type  integral        16    'hfe9c        
  pload       da(integral)    21    -             
    [0]       integral        8     'h26          
    [1]       integral        8     'h6d          
    [2]       integral        8     'h5e          
    [3]       integral        8     'h9f          
    [4]       integral        8     'hc9          
    ...       ...             ...   ...           
    [16]      integral        8     'h3e          
    [17]      integral        8     'h6c          
    [18]      integral        8     'h4           
    [19]      integral        8     'h8f          
    [20]      integral        8     'h5d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 38100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7155         
  dmac        integral        48    'h10d60ac35d42
  smac        integral        48    'hc4ab5497efa3
  ether_type  integral        16    'hfe9c        
  pload       da(integral)    21    -             
    [0]       integral        8     'h26          
    [1]       integral        8     'h6d          
    [2]       integral        8     'h5e          
    [3]       integral        8     'h9f          
    [4]       integral        8     'hc9          
    ...       ...             ...   ...           
    [16]      integral        8     'h3e          
    [17]      integral        8     'h6c          
    [18]      integral        8     'h4           
    [19]      integral        8     'h8f          
    [20]      integral        8     'h5d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 38300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7250         
  dmac        integral        48    'h10d60ac35d42
  smac        integral        48    'hc4ab5497efa3
  ether_type  integral        16    'hfe9c        
  pload       da(integral)    21    -             
    [0]       integral        8     'h26          
    [1]       integral        8     'h6d          
    [2]       integral        8     'h5e          
    [3]       integral        8     'h9f          
    [4]       integral        8     'hc9          
    ...       ...             ...   ...           
    [16]      integral        8     'h3e          
    [17]      integral        8     'h6c          
    [18]      integral        8     'h4           
    [19]      integral        8     'h8f          
    [20]      integral        8     'h5d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 38300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7250         
  dmac        integral        48    'h10d60ac35d42
  smac        integral        48    'hc4ab5497efa3
  ether_type  integral        16    'hfe9c        
  pload       da(integral)    21    -             
    [0]       integral        8     'h26          
    [1]       integral        8     'h6d          
    [2]       integral        8     'h5e          
    [3]       integral        8     'h9f          
    [4]       integral        8     'hc9          
    ...       ...             ...   ...           
    [16]      integral        8     'h3e          
    [17]      integral        8     'h6c          
    [18]      integral        8     'h4           
    [19]      integral        8     'h8f          
    [20]      integral        8     'h5d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 38500000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(46) @ 38500000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 38500000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7174                               
  dmac                         integral        48    'h1732940ff0be                      
  smac                         integral        48    'hed47ca793fbb                      
  ether_type                   integral        16    'h13b6                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'hc                                 
    [1]                        integral        8     'h93                                
    [2]                        integral        8     'h18                                
    [3]                        integral        8     'h20                                
    [4]                        integral        8     'h45                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'hbf                                
    [18]                       integral        8     'h67                                
    [19]                       integral        8     'hb5                                
    [20]                       integral        8     'h62                                
    [21]                       integral        8     'hf4                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    38500000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 38700000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7184         
  dmac        integral        48    'heb8317e68a71
  smac        integral        48    'h83b6433f221 
  ether_type  integral        16    'ha879        
  pload       da(integral)    22    -             
    [0]       integral        8     'hcd          
    [1]       integral        8     'h14          
    [2]       integral        8     'ha8          
    [3]       integral        8     'h4           
    [4]       integral        8     'h2b          
    ...       ...             ...   ...           
    [17]      integral        8     'h3c          
    [18]      integral        8     'h86          
    [19]      integral        8     'hea          
    [20]      integral        8     'ha5          
    [21]      integral        8     'h5a          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 38700000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7086         
  dmac        integral        48    'heb8317e68a71
  smac        integral        48    'h83b6433f221 
  ether_type  integral        16    'ha879        
  pload       da(integral)    22    -             
    [0]       integral        8     'hcd          
    [1]       integral        8     'h14          
    [2]       integral        8     'ha8          
    [3]       integral        8     'h4           
    [4]       integral        8     'h2b          
    ...       ...             ...   ...           
    [17]      integral        8     'h3c          
    [18]      integral        8     'h86          
    [19]      integral        8     'hea          
    [20]      integral        8     'ha5          
    [21]      integral        8     'h5a          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 38900000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7159         
  dmac        integral        48    'heb8317e68a71
  smac        integral        48    'h83b6433f221 
  ether_type  integral        16    'ha879        
  pload       da(integral)    22    -             
    [0]       integral        8     'hcd          
    [1]       integral        8     'h14          
    [2]       integral        8     'ha8          
    [3]       integral        8     'h4           
    [4]       integral        8     'h2b          
    ...       ...             ...   ...           
    [17]      integral        8     'h3c          
    [18]      integral        8     'h86          
    [19]      integral        8     'hea          
    [20]      integral        8     'ha5          
    [21]      integral        8     'h5a          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 38900000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7159         
  dmac        integral        48    'heb8317e68a71
  smac        integral        48    'h83b6433f221 
  ether_type  integral        16    'ha879        
  pload       da(integral)    22    -             
    [0]       integral        8     'hcd          
    [1]       integral        8     'h14          
    [2]       integral        8     'ha8          
    [3]       integral        8     'h4           
    [4]       integral        8     'h2b          
    ...       ...             ...   ...           
    [17]      integral        8     'h3c          
    [18]      integral        8     'h86          
    [19]      integral        8     'hea          
    [20]      integral        8     'ha5          
    [21]      integral        8     'h5a          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 39300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 39500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 39900000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 40100000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 46900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 46900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 46900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7129                               
  dmac                         integral        48    'h5cbc26ed9bfc                      
  smac                         integral        48    'hfe5013c40a51                      
  ether_type                   integral        16    'h7909                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h39                                
    [1]                        integral        8     'h9f                                
    [2]                        integral        8     'h25                                
    [3]                        integral        8     'hd1                                
    [4]                        integral        8     'h23                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'hc                                 
    [17]                       integral        8     'h1a                                
    [18]                       integral        8     'h54                                
    [19]                       integral        8     'h9a                                
    [20]                       integral        8     'ha4                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    46900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 47100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7287         
  dmac        integral        48    'h916ce8349444
  smac        integral        48    'h1c62e9fda8cb
  ether_type  integral        16    'hb94         
  pload       da(integral)    21    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h69          
    [2]       integral        8     'h5d          
    [3]       integral        8     'h5           
    [4]       integral        8     'h48          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'h67          
    [18]      integral        8     'hb9          
    [19]      integral        8     'hc7          
    [20]      integral        8     'hf1          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 47100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7192         
  dmac        integral        48    'h916ce8349444
  smac        integral        48    'h1c62e9fda8cb
  ether_type  integral        16    'hb94         
  pload       da(integral)    21    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h69          
    [2]       integral        8     'h5d          
    [3]       integral        8     'h5           
    [4]       integral        8     'h48          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'h67          
    [18]      integral        8     'hb9          
    [19]      integral        8     'hc7          
    [20]      integral        8     'hf1          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 47300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7279         
  dmac        integral        48    'h916ce8349444
  smac        integral        48    'h1c62e9fda8cb
  ether_type  integral        16    'hb94         
  pload       da(integral)    21    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h69          
    [2]       integral        8     'h5d          
    [3]       integral        8     'h5           
    [4]       integral        8     'h48          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'h67          
    [18]      integral        8     'hb9          
    [19]      integral        8     'hc7          
    [20]      integral        8     'hf1          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 47300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7279         
  dmac        integral        48    'h916ce8349444
  smac        integral        48    'h1c62e9fda8cb
  ether_type  integral        16    'hb94         
  pload       da(integral)    21    -             
    [0]       integral        8     'hf6          
    [1]       integral        8     'h69          
    [2]       integral        8     'h5d          
    [3]       integral        8     'h5           
    [4]       integral        8     'h48          
    ...       ...             ...   ...           
    [16]      integral        8     'hc1          
    [17]      integral        8     'h67          
    [18]      integral        8     'hb9          
    [19]      integral        8     'hc7          
    [20]      integral        8     'hf1          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 47700000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(46) @ 47700000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 47700000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7289                               
  dmac                         integral        48    'h189b718127c0                      
  smac                         integral        48    'h1c095e4f4afa                      
  ether_type                   integral        16    'h629e                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'he0                                
    [1]                        integral        8     'h15                                
    [2]                        integral        8     'hd2                                
    [3]                        integral        8     'h65                                
    [4]                        integral        8     'hf8                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h1                                 
    [18]                       integral        8     'h97                                
    [19]                       integral        8     'h8d                                
    [20]                       integral        8     'he9                                
    [21]                       integral        8     'hd8                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    47700000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 47900000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7269         
  dmac        integral        48    'h1732940ff0be
  smac        integral        48    'hed47ca793fbb
  ether_type  integral        16    'h13b6        
  pload       da(integral)    22    -             
    [0]       integral        8     'hc           
    [1]       integral        8     'h93          
    [2]       integral        8     'h18          
    [3]       integral        8     'h20          
    [4]       integral        8     'h45          
    ...       ...             ...   ...           
    [17]      integral        8     'hbf          
    [18]      integral        8     'h67          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h62          
    [21]      integral        8     'hf4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 47900000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7278         
  dmac        integral        48    'h1732940ff0be
  smac        integral        48    'hed47ca793fbb
  ether_type  integral        16    'h13b6        
  pload       da(integral)    22    -             
    [0]       integral        8     'hc           
    [1]       integral        8     'h93          
    [2]       integral        8     'h18          
    [3]       integral        8     'h20          
    [4]       integral        8     'h45          
    ...       ...             ...   ...           
    [17]      integral        8     'hbf          
    [18]      integral        8     'h67          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h62          
    [21]      integral        8     'hf4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 48100000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7286         
  dmac        integral        48    'h1732940ff0be
  smac        integral        48    'hed47ca793fbb
  ether_type  integral        16    'h13b6        
  pload       da(integral)    22    -             
    [0]       integral        8     'hc           
    [1]       integral        8     'h93          
    [2]       integral        8     'h18          
    [3]       integral        8     'h20          
    [4]       integral        8     'h45          
    ...       ...             ...   ...           
    [17]      integral        8     'hbf          
    [18]      integral        8     'h67          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h62          
    [21]      integral        8     'hf4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 48100000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7286         
  dmac        integral        48    'h1732940ff0be
  smac        integral        48    'hed47ca793fbb
  ether_type  integral        16    'h13b6        
  pload       da(integral)    22    -             
    [0]       integral        8     'hc           
    [1]       integral        8     'h93          
    [2]       integral        8     'h18          
    [3]       integral        8     'h20          
    [4]       integral        8     'h45          
    ...       ...             ...   ...           
    [17]      integral        8     'hbf          
    [18]      integral        8     'h67          
    [19]      integral        8     'hb5          
    [20]      integral        8     'h62          
    [21]      integral        8     'hf4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 48300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 48500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 49100000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 49300000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 55900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 55900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 55900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7294                               
  dmac                         integral        48    'h7f2c6ee7468                       
  smac                         integral        48    'h126605daecad                      
  ether_type                   integral        16    'hb66                               
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h31                                
    [1]                        integral        8     'h1a                                
    [2]                        integral        8     'hfd                                
    [3]                        integral        8     'ha9                                
    [4]                        integral        8     'h9f                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'he3                                
    [17]                       integral        8     'h4d                                
    [18]                       integral        8     'h2b                                
    [19]                       integral        8     'h4b                                
    [20]                       integral        8     'hdb                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    55900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 56100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7218         
  dmac        integral        48    'h5cbc26ed9bfc
  smac        integral        48    'hfe5013c40a51
  ether_type  integral        16    'h7909        
  pload       da(integral)    21    -             
    [0]       integral        8     'h39          
    [1]       integral        8     'h9f          
    [2]       integral        8     'h25          
    [3]       integral        8     'hd1          
    [4]       integral        8     'h23          
    ...       ...             ...   ...           
    [16]      integral        8     'hc           
    [17]      integral        8     'h1a          
    [18]      integral        8     'h54          
    [19]      integral        8     'h9a          
    [20]      integral        8     'ha4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 56100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7156         
  dmac        integral        48    'h5cbc26ed9bfc
  smac        integral        48    'hfe5013c40a51
  ether_type  integral        16    'h7909        
  pload       da(integral)    21    -             
    [0]       integral        8     'h39          
    [1]       integral        8     'h9f          
    [2]       integral        8     'h25          
    [3]       integral        8     'hd1          
    [4]       integral        8     'h23          
    ...       ...             ...   ...           
    [16]      integral        8     'hc           
    [17]      integral        8     'h1a          
    [18]      integral        8     'h54          
    [19]      integral        8     'h9a          
    [20]      integral        8     'ha4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 56300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7304         
  dmac        integral        48    'h5cbc26ed9bfc
  smac        integral        48    'hfe5013c40a51
  ether_type  integral        16    'h7909        
  pload       da(integral)    21    -             
    [0]       integral        8     'h39          
    [1]       integral        8     'h9f          
    [2]       integral        8     'h25          
    [3]       integral        8     'hd1          
    [4]       integral        8     'h23          
    ...       ...             ...   ...           
    [16]      integral        8     'hc           
    [17]      integral        8     'h1a          
    [18]      integral        8     'h54          
    [19]      integral        8     'h9a          
    [20]      integral        8     'ha4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 56300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7304         
  dmac        integral        48    'h5cbc26ed9bfc
  smac        integral        48    'hfe5013c40a51
  ether_type  integral        16    'h7909        
  pload       da(integral)    21    -             
    [0]       integral        8     'h39          
    [1]       integral        8     'h9f          
    [2]       integral        8     'h25          
    [3]       integral        8     'hd1          
    [4]       integral        8     'h23          
    ...       ...             ...   ...           
    [16]      integral        8     'hc           
    [17]      integral        8     'h1a          
    [18]      integral        8     'h54          
    [19]      integral        8     'h9a          
    [20]      integral        8     'ha4          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 56900000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(46) @ 56900000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 56900000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7298                               
  dmac                         integral        48    'h6318b03a2f78                      
  smac                         integral        48    'h26ec89a55a69                      
  ether_type                   integral        16    'h8e23                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'h20                                
    [1]                        integral        8     'hc4                                
    [2]                        integral        8     'hdf                                
    [3]                        integral        8     'h53                                
    [4]                        integral        8     'ha0                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h6d                                
    [18]                       integral        8     'hb8                                
    [19]                       integral        8     'hc1                                
    [20]                       integral        8     'ha8                                
    [21]                       integral        8     'h3c                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    56900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 57100000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7290         
  dmac        integral        48    'h189b718127c0
  smac        integral        48    'h1c095e4f4afa
  ether_type  integral        16    'h629e        
  pload       da(integral)    22    -             
    [0]       integral        8     'he0          
    [1]       integral        8     'h15          
    [2]       integral        8     'hd2          
    [3]       integral        8     'h65          
    [4]       integral        8     'hf8          
    ...       ...             ...   ...           
    [17]      integral        8     'h1           
    [18]      integral        8     'h97          
    [19]      integral        8     'h8d          
    [20]      integral        8     'he9          
    [21]      integral        8     'hd8          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 57100000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7224         
  dmac        integral        48    'h189b718127c0
  smac        integral        48    'h1c095e4f4afa
  ether_type  integral        16    'h629e        
  pload       da(integral)    22    -             
    [0]       integral        8     'he0          
    [1]       integral        8     'h15          
    [2]       integral        8     'hd2          
    [3]       integral        8     'h65          
    [4]       integral        8     'hf8          
    ...       ...             ...   ...           
    [17]      integral        8     'h1           
    [18]      integral        8     'h97          
    [19]      integral        8     'h8d          
    [20]      integral        8     'he9          
    [21]      integral        8     'hd8          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 57300000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7293         
  dmac        integral        48    'h189b718127c0
  smac        integral        48    'h1c095e4f4afa
  ether_type  integral        16    'h629e        
  pload       da(integral)    22    -             
    [0]       integral        8     'he0          
    [1]       integral        8     'h15          
    [2]       integral        8     'hd2          
    [3]       integral        8     'h65          
    [4]       integral        8     'hf8          
    ...       ...             ...   ...           
    [17]      integral        8     'h1           
    [18]      integral        8     'h97          
    [19]      integral        8     'h8d          
    [20]      integral        8     'he9          
    [21]      integral        8     'hd8          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 57300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_scoreboard.sv(39) @ 57300000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7293         
  dmac        integral        48    'h189b718127c0
  smac        integral        48    'h1c095e4f4afa
  ether_type  integral        16    'h629e        
  pload       da(integral)    22    -             
    [0]       integral        8     'he0          
    [1]       integral        8     'h15          
    [2]       integral        8     'hd2          
    [3]       integral        8     'h65          
    [4]       integral        8     'hf8          
    ...       ...             ...   ...           
    [17]      integral        8     'h1           
    [18]      integral        8     'h97          
    [19]      integral        8     'h8d          
    [20]      integral        8     'he9          
    [21]      integral        8     'hd8          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 57500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 58300000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 58500000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 64900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 64900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 64900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7309                               
  dmac                         integral        48    'h7d10c8371d8a                      
  smac                         integral        48    'hd9aa8de22550                      
  ether_type                   integral        16    'hbc51                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h97                                
    [1]                        integral        8     'h49                                
    [2]                        integral        8     'he3                                
    [3]                        integral        8     'h7                                 
    [4]                        integral        8     'h44                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'hc0                                
    [17]                       integral        8     'hf2                                
    [18]                       integral        8     'h6e                                
    [19]                       integral        8     'hf6                                
    [20]                       integral        8     'h3d                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    64900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 65100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7238         
  dmac        integral        48    'h7f2c6ee7468 
  smac        integral        48    'h126605daecad
  ether_type  integral        16    'hb66         
  pload       da(integral)    21    -             
    [0]       integral        8     'h31          
    [1]       integral        8     'h1a          
    [2]       integral        8     'hfd          
    [3]       integral        8     'ha9          
    [4]       integral        8     'h9f          
    ...       ...             ...   ...           
    [16]      integral        8     'he3          
    [17]      integral        8     'h4d          
    [18]      integral        8     'h2b          
    [19]      integral        8     'h4b          
    [20]      integral        8     'hdb          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 65100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7176         
  dmac        integral        48    'h7f2c6ee7468 
  smac        integral        48    'h126605daecad
  ether_type  integral        16    'hb66         
  pload       da(integral)    21    -             
    [0]       integral        8     'h31          
    [1]       integral        8     'h1a          
    [2]       integral        8     'hfd          
    [3]       integral        8     'ha9          
    [4]       integral        8     'h9f          
    ...       ...             ...   ...           
    [16]      integral        8     'he3          
    [17]      integral        8     'h4d          
    [18]      integral        8     'h2b          
    [19]      integral        8     'h4b          
    [20]      integral        8     'hdb          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 65300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7295         
  dmac        integral        48    'h7f2c6ee7468 
  smac        integral        48    'h126605daecad
  ether_type  integral        16    'hb66         
  pload       da(integral)    21    -             
    [0]       integral        8     'h31          
    [1]       integral        8     'h1a          
    [2]       integral        8     'hfd          
    [3]       integral        8     'ha9          
    [4]       integral        8     'h9f          
    ...       ...             ...   ...           
    [16]      integral        8     'he3          
    [17]      integral        8     'h4d          
    [18]      integral        8     'h2b          
    [19]      integral        8     'h4b          
    [20]      integral        8     'hdb          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 65300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7295         
  dmac        integral        48    'h7f2c6ee7468 
  smac        integral        48    'h126605daecad
  ether_type  integral        16    'hb66         
  pload       da(integral)    21    -             
    [0]       integral        8     'h31          
    [1]       integral        8     'h1a          
    [2]       integral        8     'hfd          
    [3]       integral        8     'ha9          
    [4]       integral        8     'h9f          
    ...       ...             ...   ...           
    [16]      integral        8     'he3          
    [17]      integral        8     'h4d          
    [18]      integral        8     'h2b          
    [19]      integral        8     'h4b          
    [20]      integral        8     'hdb          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 66100000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(46) @ 66100000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 66100000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7207                               
  dmac                         integral        48    'h8f21503b07e4                      
  smac                         integral        48    'h120d7a2c8edb                      
  ether_type                   integral        16    'h6270                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'h1a                                
    [1]                        integral        8     'hc6                                
    [2]                        integral        8     'h71                                
    [3]                        integral        8     'h9                                 
    [4]                        integral        8     'h4f                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'he7                                
    [18]                       integral        8     'ha                                 
    [19]                       integral        8     'h10                                
    [20]                       integral        8     'hd3                                
    [21]                       integral        8     'hff                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    66100000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 66300000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7228         
  dmac        integral        48    'h6318b03a2f78
  smac        integral        48    'h26ec89a55a69
  ether_type  integral        16    'h8e23        
  pload       da(integral)    22    -             
    [0]       integral        8     'h20          
    [1]       integral        8     'hc4          
    [2]       integral        8     'hdf          
    [3]       integral        8     'h53          
    [4]       integral        8     'ha0          
    ...       ...             ...   ...           
    [17]      integral        8     'h6d          
    [18]      integral        8     'hb8          
    [19]      integral        8     'hc1          
    [20]      integral        8     'ha8          
    [21]      integral        8     'h3c          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 66300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_model.sv(30) @ 66300000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7090         
  dmac        integral        48    'h6318b03a2f78
  smac        integral        48    'h26ec89a55a69
  ether_type  integral        16    'h8e23        
  pload       da(integral)    22    -             
    [0]       integral        8     'h20          
    [1]       integral        8     'hc4          
    [2]       integral        8     'hdf          
    [3]       integral        8     'h53          
    [4]       integral        8     'ha0          
    ...       ...             ...   ...           
    [17]      integral        8     'h6d          
    [18]      integral        8     'hb8          
    [19]      integral        8     'hc1          
    [20]      integral        8     'ha8          
    [21]      integral        8     'h3c          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 66500000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7272         
  dmac        integral        48    'h6318b03a2f78
  smac        integral        48    'h26ec89a55a69
  ether_type  integral        16    'h8e23        
  pload       da(integral)    22    -             
    [0]       integral        8     'h20          
    [1]       integral        8     'hc4          
    [2]       integral        8     'hdf          
    [3]       integral        8     'h53          
    [4]       integral        8     'ha0          
    ...       ...             ...   ...           
    [17]      integral        8     'h6d          
    [18]      integral        8     'hb8          
    [19]      integral        8     'hc1          
    [20]      integral        8     'ha8          
    [21]      integral        8     'h3c          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 66500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_scoreboard.sv(39) @ 66500000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7272         
  dmac        integral        48    'h6318b03a2f78
  smac        integral        48    'h26ec89a55a69
  ether_type  integral        16    'h8e23        
  pload       da(integral)    22    -             
    [0]       integral        8     'h20          
    [1]       integral        8     'hc4          
    [2]       integral        8     'hdf          
    [3]       integral        8     'h53          
    [4]       integral        8     'ha0          
    ...       ...             ...   ...           
    [17]      integral        8     'h6d          
    [18]      integral        8     'hb8          
    [19]      integral        8     'hc1          
    [20]      integral        8     'ha8          
    [21]      integral        8     'h3c          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 67500000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 67700000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 73900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 73900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 73900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7163                               
  dmac                         integral        48    'hc7e82ac79761                      
  smac                         integral        48    'heaa2437a1b98                      
  ether_type                   integral        16    'h50e6                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h92                                
    [1]                        integral        8     'h7c                                
    [2]                        integral        8     'h12                                
    [3]                        integral        8     'h8e                                
    [4]                        integral        8     'h80                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'h28                                
    [17]                       integral        8     'h56                                
    [18]                       integral        8     'hff                                
    [19]                       integral        8     'hae                                
    [20]                       integral        8     'h6b                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    73900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 74100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7297         
  dmac        integral        48    'h7d10c8371d8a
  smac        integral        48    'hd9aa8de22550
  ether_type  integral        16    'hbc51        
  pload       da(integral)    21    -             
    [0]       integral        8     'h97          
    [1]       integral        8     'h49          
    [2]       integral        8     'he3          
    [3]       integral        8     'h7           
    [4]       integral        8     'h44          
    ...       ...             ...   ...           
    [16]      integral        8     'hc0          
    [17]      integral        8     'hf2          
    [18]      integral        8     'h6e          
    [19]      integral        8     'hf6          
    [20]      integral        8     'h3d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 74100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7185         
  dmac        integral        48    'h7d10c8371d8a
  smac        integral        48    'hd9aa8de22550
  ether_type  integral        16    'hbc51        
  pload       da(integral)    21    -             
    [0]       integral        8     'h97          
    [1]       integral        8     'h49          
    [2]       integral        8     'he3          
    [3]       integral        8     'h7           
    [4]       integral        8     'h44          
    ...       ...             ...   ...           
    [16]      integral        8     'hc0          
    [17]      integral        8     'hf2          
    [18]      integral        8     'h6e          
    [19]      integral        8     'hf6          
    [20]      integral        8     'h3d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 74300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7263         
  dmac        integral        48    'h7d10c8371d8a
  smac        integral        48    'hd9aa8de22550
  ether_type  integral        16    'hbc51        
  pload       da(integral)    21    -             
    [0]       integral        8     'h97          
    [1]       integral        8     'h49          
    [2]       integral        8     'he3          
    [3]       integral        8     'h7           
    [4]       integral        8     'h44          
    ...       ...             ...   ...           
    [16]      integral        8     'hc0          
    [17]      integral        8     'hf2          
    [18]      integral        8     'h6e          
    [19]      integral        8     'hf6          
    [20]      integral        8     'h3d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 74300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7263         
  dmac        integral        48    'h7d10c8371d8a
  smac        integral        48    'hd9aa8de22550
  ether_type  integral        16    'hbc51        
  pload       da(integral)    21    -             
    [0]       integral        8     'h97          
    [1]       integral        8     'h49          
    [2]       integral        8     'he3          
    [3]       integral        8     'h7           
    [4]       integral        8     'h44          
    ...       ...             ...   ...           
    [16]      integral        8     'hc0          
    [17]      integral        8     'hf2          
    [18]      integral        8     'h6e          
    [19]      integral        8     'hf6          
    [20]      integral        8     'h3d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 75300000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(44) @ 75300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_case0.sv(46) @ 75300000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 75300000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7276                               
  dmac                         integral        48    'h43f5183b106                       
  smac                         integral        48    'hd9510233c77e                      
  ether_type                   integral        16    'h135a                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'h80                                
    [1]                        integral        8     'hf6                                
    [2]                        integral        8     'h57                                
    [3]                        integral        8     'h68                                
    [4]                        integral        8     'hf3                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h8c                                
    [18]                       integral        8     'h4c                                
    [19]                       integral        8     'hbc                                
    [20]                       integral        8     'h35                                
    [21]                       integral        8     'h41                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    75300000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 75500000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7281         
  dmac        integral        48    'h8f21503b07e4
  smac        integral        48    'h120d7a2c8edb
  ether_type  integral        16    'h6270        
  pload       da(integral)    22    -             
    [0]       integral        8     'h1a          
    [1]       integral        8     'hc6          
    [2]       integral        8     'h71          
    [3]       integral        8     'h9           
    [4]       integral        8     'h4f          
    ...       ...             ...   ...           
    [17]      integral        8     'he7          
    [18]      integral        8     'ha           
    [19]      integral        8     'h10          
    [20]      integral        8     'hd3          
    [21]      integral        8     'hff          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 75500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_model.sv(30) @ 75500000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7177         
  dmac        integral        48    'h8f21503b07e4
  smac        integral        48    'h120d7a2c8edb
  ether_type  integral        16    'h6270        
  pload       da(integral)    22    -             
    [0]       integral        8     'h1a          
    [1]       integral        8     'hc6          
    [2]       integral        8     'h71          
    [3]       integral        8     'h9           
    [4]       integral        8     'h4f          
    ...       ...             ...   ...           
    [17]      integral        8     'he7          
    [18]      integral        8     'ha           
    [19]      integral        8     'h10          
    [20]      integral        8     'hd3          
    [21]      integral        8     'hff          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 75700000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7252         
  dmac        integral        48    'h8f21503b07e4
  smac        integral        48    'h120d7a2c8edb
  ether_type  integral        16    'h6270        
  pload       da(integral)    22    -             
    [0]       integral        8     'h1a          
    [1]       integral        8     'hc6          
    [2]       integral        8     'h71          
    [3]       integral        8     'h9           
    [4]       integral        8     'h4f          
    ...       ...             ...   ...           
    [17]      integral        8     'he7          
    [18]      integral        8     'ha           
    [19]      integral        8     'h10          
    [20]      integral        8     'hd3          
    [21]      integral        8     'hff          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 75700000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7252         
  dmac        integral        48    'h8f21503b07e4
  smac        integral        48    'h120d7a2c8edb
  ether_type  integral        16    'h6270        
  pload       da(integral)    22    -             
    [0]       integral        8     'h1a          
    [1]       integral        8     'hc6          
    [2]       integral        8     'h71          
    [3]       integral        8     'h9           
    [4]       integral        8     'h4f          
    ...       ...             ...   ...           
    [17]      integral        8     'he7          
    [18]      integral        8     'ha           
    [19]      integral        8     'h10          
    [20]      integral        8     'hd3          
    [21]      integral        8     'hff          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 76700000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 76900000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 82900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 82900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 82900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7206                               
  dmac                         integral        48    'he6d4ee9fe1ed                      
  smac                         integral        48    'h973b29c22b57                      
  ether_type                   integral        16    'h4546                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h1b                                
    [1]                        integral        8     'ha5                                
    [2]                        integral        8     'h16                                
    [3]                        integral        8     'h80                                
    [4]                        integral        8     'hef                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'h97                                
    [17]                       integral        8     'heb                                
    [18]                       integral        8     'he8                                
    [19]                       integral        8     'h33                                
    [20]                       integral        8     'h7d                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    82900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 83100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7301         
  dmac        integral        48    'hc7e82ac79761
  smac        integral        48    'heaa2437a1b98
  ether_type  integral        16    'h50e6        
  pload       da(integral)    21    -             
    [0]       integral        8     'h92          
    [1]       integral        8     'h7c          
    [2]       integral        8     'h12          
    [3]       integral        8     'h8e          
    [4]       integral        8     'h80          
    ...       ...             ...   ...           
    [16]      integral        8     'h28          
    [17]      integral        8     'h56          
    [18]      integral        8     'hff          
    [19]      integral        8     'hae          
    [20]      integral        8     'h6b          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 83100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7154         
  dmac        integral        48    'hc7e82ac79761
  smac        integral        48    'heaa2437a1b98
  ether_type  integral        16    'h50e6        
  pload       da(integral)    21    -             
    [0]       integral        8     'h92          
    [1]       integral        8     'h7c          
    [2]       integral        8     'h12          
    [3]       integral        8     'h8e          
    [4]       integral        8     'h80          
    ...       ...             ...   ...           
    [16]      integral        8     'h28          
    [17]      integral        8     'h56          
    [18]      integral        8     'hff          
    [19]      integral        8     'hae          
    [20]      integral        8     'h6b          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 83300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7175         
  dmac        integral        48    'hc7e82ac79761
  smac        integral        48    'heaa2437a1b98
  ether_type  integral        16    'h50e6        
  pload       da(integral)    21    -             
    [0]       integral        8     'h92          
    [1]       integral        8     'h7c          
    [2]       integral        8     'h12          
    [3]       integral        8     'h8e          
    [4]       integral        8     'h80          
    ...       ...             ...   ...           
    [16]      integral        8     'h28          
    [17]      integral        8     'h56          
    [18]      integral        8     'hff          
    [19]      integral        8     'hae          
    [20]      integral        8     'h6b          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 83300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7175         
  dmac        integral        48    'hc7e82ac79761
  smac        integral        48    'heaa2437a1b98
  ether_type  integral        16    'h50e6        
  pload       da(integral)    21    -             
    [0]       integral        8     'h92          
    [1]       integral        8     'h7c          
    [2]       integral        8     'h12          
    [3]       integral        8     'h8e          
    [4]       integral        8     'h80          
    ...       ...             ...   ...           
    [16]      integral        8     'h28          
    [17]      integral        8     'h56          
    [18]      integral        8     'hff          
    [19]      integral        8     'hae          
    [20]      integral        8     'h6b          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 84300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 84500000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(44) @ 84500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_case0.sv(46) @ 84500000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 84500000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7183                               
  dmac                         integral        48    'hce44b4142add                      
  smac                         integral        48    'h133eb95b6baf                      
  ether_type                   integral        16    'h6600                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'h78                                
    [1]                        integral        8     'ha2                                
    [2]                        integral        8     'hcc                                
    [3]                        integral        8     'h10                                
    [4]                        integral        8     'hfd                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'ha9                                
    [18]                       integral        8     'h62                                
    [19]                       integral        8     'hd4                                
    [20]                       integral        8     'h6f                                
    [21]                       integral        8     'h17                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    84500000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 84700000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7150         
  dmac        integral        48    'h43f5183b106 
  smac        integral        48    'hd9510233c77e
  ether_type  integral        16    'h135a        
  pload       da(integral)    22    -             
    [0]       integral        8     'h80          
    [1]       integral        8     'hf6          
    [2]       integral        8     'h57          
    [3]       integral        8     'h68          
    [4]       integral        8     'hf3          
    ...       ...             ...   ...           
    [17]      integral        8     'h8c          
    [18]      integral        8     'h4c          
    [19]      integral        8     'hbc          
    [20]      integral        8     'h35          
    [21]      integral        8     'h41          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 84700000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7284         
  dmac        integral        48    'h43f5183b106 
  smac        integral        48    'hd9510233c77e
  ether_type  integral        16    'h135a        
  pload       da(integral)    22    -             
    [0]       integral        8     'h80          
    [1]       integral        8     'hf6          
    [2]       integral        8     'h57          
    [3]       integral        8     'h68          
    [4]       integral        8     'hf3          
    ...       ...             ...   ...           
    [17]      integral        8     'h8c          
    [18]      integral        8     'h4c          
    [19]      integral        8     'hbc          
    [20]      integral        8     'h35          
    [21]      integral        8     'h41          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 84900000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7219         
  dmac        integral        48    'h43f5183b106 
  smac        integral        48    'hd9510233c77e
  ether_type  integral        16    'h135a        
  pload       da(integral)    22    -             
    [0]       integral        8     'h80          
    [1]       integral        8     'hf6          
    [2]       integral        8     'h57          
    [3]       integral        8     'h68          
    [4]       integral        8     'hf3          
    ...       ...             ...   ...           
    [17]      integral        8     'h8c          
    [18]      integral        8     'h4c          
    [19]      integral        8     'hbc          
    [20]      integral        8     'h35          
    [21]      integral        8     'h41          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 84900000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7219         
  dmac        integral        48    'h43f5183b106 
  smac        integral        48    'hd9510233c77e
  ether_type  integral        16    'h135a        
  pload       da(integral)    22    -             
    [0]       integral        8     'h80          
    [1]       integral        8     'hf6          
    [2]       integral        8     'h57          
    [3]       integral        8     'h68          
    [4]       integral        8     'hf3          
    ...       ...             ...   ...           
    [17]      integral        8     'h8c          
    [18]      integral        8     'h4c          
    [19]      integral        8     'hbc          
    [20]      integral        8     'h35          
    [21]      integral        8     'h41          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 85900000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 86100000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 91900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 91900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 91900000: uvm_test_top.env0.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7275                               
  dmac                         integral        48    'h5c4c13bffd2e                      
  smac                         integral        48    'h64943c0b4ad3                      
  ether_type                   integral        16    'h5f40                              
  pload                        da(integral)    21    -                                   
    [0]                        integral        8     'h3c                                
    [1]                        integral        8     'h58                                
    [2]                        integral        8     'h1e                                
    [3]                        integral        8     'h78                                
    [4]                        integral        8     'h28                                
    ...                        ...             ...   ...                                 
    [16]                       integral        8     'h54                                
    [17]                       integral        8     'h88                                
    [18]                       integral        8     'h9b                                
    [19]                       integral        8     'h62                                
    [20]                       integral        8     'h4d                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    91900000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv0_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env0.i_agt.sqr.drv0_seq
  sequencer                    string          27    uvm_test_top.env0.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 92100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7190         
  dmac        integral        48    'he6d4ee9fe1ed
  smac        integral        48    'h973b29c22b57
  ether_type  integral        16    'h4546        
  pload       da(integral)    21    -             
    [0]       integral        8     'h1b          
    [1]       integral        8     'ha5          
    [2]       integral        8     'h16          
    [3]       integral        8     'h80          
    [4]       integral        8     'hef          
    ...       ...             ...   ...           
    [16]      integral        8     'h97          
    [17]      integral        8     'heb          
    [18]      integral        8     'he8          
    [19]      integral        8     'h33          
    [20]      integral        8     'h7d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 92100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7234         
  dmac        integral        48    'he6d4ee9fe1ed
  smac        integral        48    'h973b29c22b57
  ether_type  integral        16    'h4546        
  pload       da(integral)    21    -             
    [0]       integral        8     'h1b          
    [1]       integral        8     'ha5          
    [2]       integral        8     'h16          
    [3]       integral        8     'h80          
    [4]       integral        8     'hef          
    ...       ...             ...   ...           
    [16]      integral        8     'h97          
    [17]      integral        8     'heb          
    [18]      integral        8     'he8          
    [19]      integral        8     'h33          
    [20]      integral        8     'h7d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 92300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7261         
  dmac        integral        48    'he6d4ee9fe1ed
  smac        integral        48    'h973b29c22b57
  ether_type  integral        16    'h4546        
  pload       da(integral)    21    -             
    [0]       integral        8     'h1b          
    [1]       integral        8     'ha5          
    [2]       integral        8     'h16          
    [3]       integral        8     'h80          
    [4]       integral        8     'hef          
    ...       ...             ...   ...           
    [16]      integral        8     'h97          
    [17]      integral        8     'heb          
    [18]      integral        8     'he8          
    [19]      integral        8     'h33          
    [20]      integral        8     'h7d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 92300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7261         
  dmac        integral        48    'he6d4ee9fe1ed
  smac        integral        48    'h973b29c22b57
  ether_type  integral        16    'h4546        
  pload       da(integral)    21    -             
    [0]       integral        8     'h1b          
    [1]       integral        8     'ha5          
    [2]       integral        8     'h16          
    [3]       integral        8     'h80          
    [4]       integral        8     'hef          
    ...       ...             ...   ...           
    [16]      integral        8     'h97          
    [17]      integral        8     'heb          
    [18]      integral        8     'he8          
    [19]      integral        8     'h33          
    [20]      integral        8     'h7d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 93300000: uvm_test_top.env0.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 93500000: uvm_test_top.env0.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 93700000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(46) @ 93700000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
UVM_INFO my_driver.sv(38) @ 93700000: uvm_test_top.env1.i_agt.drv [my_driver] begin to drive one pkt
-----------------------------------------------------------------------------------------
Name                           Type            Size  Value                               
-----------------------------------------------------------------------------------------
m_trans                        my_transaction  -     @7167                               
  dmac                         integral        48    'h6e0277ec7569                      
  smac                         integral        48    'h96e29e13cd86                      
  ether_type                   integral        16    'h9c50                              
  pload                        da(integral)    22    -                                   
    [0]                        integral        8     'h5                                 
    [1]                        integral        8     'h51                                
    [2]                        integral        8     'h8b                                
    [3]                        integral        8     'he0                                
    [4]                        integral        8     'h9e                                
    ...                        ...             ...   ...                                 
    [17]                       integral        8     'h85                                
    [18]                       integral        8     'hc7                                
    [19]                       integral        8     'hf8                                
    [20]                       integral        8     'h75                                
    [21]                       integral        8     'h37                                
  crc                          integral        32    'h0                                 
  begin_time                   time            64    93700000                            
  depth                        int             32    'd2                                 
  parent sequence (name)       string          8     drv1_seq                            
  parent sequence (full name)  string          36    uvm_test_top.env1.i_agt.sqr.drv1_seq
  sequencer                    string          27    uvm_test_top.env1.i_agt.sqr         
-----------------------------------------------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 93900000: uvm_test_top.env1.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7305         
  dmac        integral        48    'hce44b4142add
  smac        integral        48    'h133eb95b6baf
  ether_type  integral        16    'h6600        
  pload       da(integral)    22    -             
    [0]       integral        8     'h78          
    [1]       integral        8     'ha2          
    [2]       integral        8     'hcc          
    [3]       integral        8     'h10          
    [4]       integral        8     'hfd          
    ...       ...             ...   ...           
    [17]      integral        8     'ha9          
    [18]      integral        8     'h62          
    [19]      integral        8     'hd4          
    [20]      integral        8     'h6f          
    [21]      integral        8     'h17          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 93900000: uvm_test_top.env1.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7077         
  dmac        integral        48    'hce44b4142add
  smac        integral        48    'h133eb95b6baf
  ether_type  integral        16    'h6600        
  pload       da(integral)    22    -             
    [0]       integral        8     'h78          
    [1]       integral        8     'ha2          
    [2]       integral        8     'hcc          
    [3]       integral        8     'h10          
    [4]       integral        8     'hfd          
    ...       ...             ...   ...           
    [17]      integral        8     'ha9          
    [18]      integral        8     'h62          
    [19]      integral        8     'hd4          
    [20]      integral        8     'h6f          
    [21]      integral        8     'h17          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 94100000: uvm_test_top.env1.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7093         
  dmac        integral        48    'hce44b4142add
  smac        integral        48    'h133eb95b6baf
  ether_type  integral        16    'h6600        
  pload       da(integral)    22    -             
    [0]       integral        8     'h78          
    [1]       integral        8     'ha2          
    [2]       integral        8     'hcc          
    [3]       integral        8     'h10          
    [4]       integral        8     'hfd          
    ...       ...             ...   ...           
    [17]      integral        8     'ha9          
    [18]      integral        8     'h62          
    [19]      integral        8     'hd4          
    [20]      integral        8     'h6f          
    [21]      integral        8     'h17          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 94100000: uvm_test_top.env1.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7093         
  dmac        integral        48    'hce44b4142add
  smac        integral        48    'h133eb95b6baf
  ether_type  integral        16    'h6600        
  pload       da(integral)    22    -             
    [0]       integral        8     'h78          
    [1]       integral        8     'ha2          
    [2]       integral        8     'hcc          
    [3]       integral        8     'h10          
    [4]       integral        8     'hfd          
    ...       ...             ...   ...           
    [17]      integral        8     'ha9          
    [18]      integral        8     'h62          
    [19]      integral        8     'hd4          
    [20]      integral        8     'h6f          
    [21]      integral        8     'h17          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(44) @ 95100000: uvm_test_top.env1.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(44) @ 95300000: uvm_test_top.env1.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(49) @ 100900000: uvm_test_top.env0.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(24) @ 100900000: uvm_test_top.env0.i_agt.sqr@@drv0_seq [drv0_seq] send one transaction
UVM_INFO my_monitor.sv(59) @ 101100000: uvm_test_top.env0.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7259         
  dmac        integral        48    'h5c4c13bffd2e
  smac        integral        48    'h64943c0b4ad3
  ether_type  integral        16    'h5f40        
  pload       da(integral)    21    -             
    [0]       integral        8     'h3c          
    [1]       integral        8     'h58          
    [2]       integral        8     'h1e          
    [3]       integral        8     'h78          
    [4]       integral        8     'h28          
    ...       ...             ...   ...           
    [16]      integral        8     'h54          
    [17]      integral        8     'h88          
    [18]      integral        8     'h9b          
    [19]      integral        8     'h62          
    [20]      integral        8     'h4d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_model.sv(30) @ 101100000: uvm_test_top.env0.mdl [my_model] get one transaction, copy, print and send it to scb:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
new_tr        my_transaction  -     @7165         
  dmac        integral        48    'h5c4c13bffd2e
  smac        integral        48    'h64943c0b4ad3
  ether_type  integral        16    'h5f40        
  pload       da(integral)    21    -             
    [0]       integral        8     'h3c          
    [1]       integral        8     'h58          
    [2]       integral        8     'h1e          
    [3]       integral        8     'h78          
    [4]       integral        8     'h28          
    ...       ...             ...   ...           
    [16]      integral        8     'h54          
    [17]      integral        8     'h88          
    [18]      integral        8     'h9b          
    [19]      integral        8     'h62          
    [20]      integral        8     'h4d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_monitor.sv(59) @ 101300000: uvm_test_top.env0.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7251         
  dmac        integral        48    'h5c4c13bffd2e
  smac        integral        48    'h64943c0b4ad3
  ether_type  integral        16    'h5f40        
  pload       da(integral)    21    -             
    [0]       integral        8     'h3c          
    [1]       integral        8     'h58          
    [2]       integral        8     'h1e          
    [3]       integral        8     'h78          
    [4]       integral        8     'h28          
    ...       ...             ...   ...           
    [16]      integral        8     'h54          
    [17]      integral        8     'h88          
    [18]      integral        8     'h9b          
    [19]      integral        8     'h62          
    [20]      integral        8     'h4d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_scoreboard.sv(39) @ 101300000: uvm_test_top.env0.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value         
--------------------------------------------------
tr            my_transaction  -     @7251         
  dmac        integral        48    'h5c4c13bffd2e
  smac        integral        48    'h64943c0b4ad3
  ether_type  integral        16    'h5f40        
  pload       da(integral)    21    -             
    [0]       integral        8     'h3c          
    [1]       integral        8     'h58          
    [2]       integral        8     'h1e          
    [3]       integral        8     'h78          
    [4]       integral        8     'h28          
    ...       ...             ...   ...           
    [16]      integral        8     'h54          
    [17]      integral        8     'h88          
    [18]      integral        8     'h9b          
    [19]      integral        8     'h62          
    [20]      integral        8     'h4d          
  crc         integral        32    'h0           
--------------------------------------------------
UVM_INFO my_driver.sv(49) @ 102900000: uvm_test_top.env1.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_case0.sv(46) @ 102900000: uvm_test_top.env1.i_agt.sqr@@drv1_seq [drv1_seq] send one transaction
TEST CASE PASSED
```
