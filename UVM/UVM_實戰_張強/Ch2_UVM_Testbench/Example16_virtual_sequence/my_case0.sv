`include "base_test.sv"
/*
  2 個 seq:       drv0_seq, drv1_seq
  1 個 base_test: my_case0
*/

event send_over;//global event

class drv0_seq extends uvm_sequence #(my_transaction);
  my_transaction m_trans;

  function new(string name = "drv0_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    if(starting_phase != null)
      starting_phase.raise_objection(this);
    `uvm_info("drv0_seq", "send the first long payload tran", UVM_MEDIUM)       // 先發送 payload 為 25 的 transaction (共 1 筆)
    `uvm_do_with(m_trans, {m_trans.pload.size == 25;})
    ->send_over;    // 要送完長 trans 才 trigger event
    repeat (10) begin
      `uvm_do_with(m_trans, {m_trans.pload.size == 21;})
      `uvm_info("drv0_seq", "send one transaction", UVM_MEDIUM)                 // 再發送 payload 為 21 的 transaction (共 10 筆)
    end
    if(starting_phase != null)
      starting_phase.drop_objection(this);
  endtask

  `uvm_object_utils(drv0_seq)
endclass

class drv1_seq extends uvm_sequence #(my_transaction);
  my_transaction m_trans;

  function new(string name = "drv1_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    if(starting_phase != null)
      starting_phase.raise_objection(this);
    @send_over;    // 當 event trigger 才能送 drv1_seq
    repeat (10) begin
      `uvm_do_with(m_trans, {m_trans.pload.size == 22;})
      `uvm_info("drv1_seq", "send one transaction", UVM_MEDIUM)                 // 發送 payload 為 22 的 transaction (共 10 筆)
    end
    if(starting_phase != null)
      starting_phase.drop_objection(this);
  endtask

  `uvm_object_utils(drv1_seq)
endclass

class my_case0 extends base_test;
  my_env env0;
  my_env env1;    // 在 test 中再額外實例化一個 my_env

  function new(string name = "my_case0", uvm_component parent = null);
    super.new(name, parent);
    `uvm_info("my_case0", "my_case0 base test is new", UVM_LOW);
    // 2 個 env
    env0 = my_env::type_id::create("env0", this);
    env1 = my_env::type_id::create("env1", this);
  endfunction

  extern virtual function void build_phase(uvm_phase phase);

  `uvm_component_utils(my_case0)
endclass

function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);
  /* 
    設定各別的 default_sequence
    drv0_seq => env0.i_agt.sqr.main_phase
    drv1_seq => env1.i_agt.sqr.main_phase
  */
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env0.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          drv0_seq::type_id::get());
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env1.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          drv1_seq::type_id::get());
endfunction
