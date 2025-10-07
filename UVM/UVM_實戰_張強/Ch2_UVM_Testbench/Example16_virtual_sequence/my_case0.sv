`include "base_test.sv"
`include "my_vsqr.sv"
class drv0_seq extends uvm_sequence #(my_transaction);      // 改成只傳輸 m_trans.pload.size == 21 的 tran (共 10 筆)
  my_transaction m_trans;

  function new(string name = "drv0_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat (10) begin
      `uvm_do_with(m_trans, {m_trans.pload.size == 21;})
      `uvm_info("drv0_seq", "send one transaction", UVM_MEDIUM)
    end
  endtask

  `uvm_object_utils(drv0_seq)
endclass

class drv1_seq extends uvm_sequence #(my_transaction);      // 改成只傳輸 m_trans.pload.size == 22 的 tran (共 10 筆)
  my_transaction m_trans;

  function new(string name = "drv1_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat (10) begin
      `uvm_do_with(m_trans, {m_trans.pload.size == 22;})
      `uvm_info("drv1_seq", "send one transaction", UVM_MEDIUM)
    end
  endtask

  `uvm_object_utils(drv1_seq)
endclass

// 增加一個 virtual sequence
class case0_vseq extends uvm_sequence #(my_transaction);
  `uvm_object_utils(case0_vseq)
  `uvm_declare_p_sequencer(my_vsqr)   // p_sequencer 轉成 my_vsqr 類別

  function new(string name = "case0_vseq");
    super.new(name);
  endfunction
  
  virtual task body();
    my_transaction m_trans;
    drv0_seq seq0;
    drv1_seq seq1;

    if(starting_phase != null)
      starting_phase.raise_objection(this);

    `uvm_do_on_with(m_trans, p_sequencer.p_sqr0, {m_trans.pload.size == 25;})
    `uvm_info("vseq", "send one longest packet on p_sequencer.p_sqr0", UVM_MEDIUM)
    fork
      `uvm_do_on(seq0, p_sequencer.p_sqr0);
      `uvm_do_on(seq1, p_sequencer.p_sqr1);
    join
    #100;

    if(starting_phase != null)
      starting_phase.drop_objection(this);
  endtask
endclass

class my_case0 extends base_test;
  my_env env0;
  my_env env1;
  my_vsqr v_sqr;

  function new(string name = "my_case0", uvm_component parent = null);
    super.new(name, parent);
    `uvm_info("my_case0", "my_case0 base test is new", UVM_LOW);
    env0 = my_env::type_id::create("env0", this);
    env1 = my_env::type_id::create("env1", this);
    v_sqr = my_vsqr::type_id::create("v_sqr", this);    // 實例化 vsqr
  endfunction

  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void build_phase(uvm_phase phase);

  `uvm_component_utils(my_case0)
endclass

function void my_case0::connect_phase(uvm_phase phase);
  // 並將對應的 sequencer 賦值給 vsqr 中的 sequencer 的指標
  v_sqr.p_sqr0 = env0.i_agt.sqr;
  v_sqr.p_sqr1 = env1.i_agt.sqr;
endfunction

function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // 僅需要設定 v_sqr 的 default_sequence 為 case0_vseq
  // uvm_config_db#(uvm_object_wrapper)::set(this,
  //                                         "env0.i_agt.sqr.main_phase",
  //                                         "default_sequence",
  //                                         drv0_seq::type_id::get());
  // uvm_config_db#(uvm_object_wrapper)::set(this,
  //                                         "env1.i_agt.sqr.main_phase",
  //                                         "default_sequence",
  //                                         drv1_seq::type_id::get());
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "v_sqr.main_phase",
                                          "default_sequence",
                                          case0_vseq::type_id::get());
endfunction
