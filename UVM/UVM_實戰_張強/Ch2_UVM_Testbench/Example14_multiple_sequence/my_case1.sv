class case1_sequence extends uvm_sequence #(my_transaction);
    my_transaction m_trans;

    function new(string name = "my_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info("my_case1", "my_case1's my_sequence", UVM_LOW);
        if (starting_phase != null)
          starting_phase.raise_objection(this);
        repeat (10) begin
          `uvm_do_with(m_trans, { m_trans.pload.size() == 60; })  // 相較於 case0 差在 case1_sequence 中出現了 uvm_do_with 宏，它是 uvm_do 系列宏中的一個，用於在隨機化時提供對某些欄位的約束。
        end
        #100;   
        if (starting_phase != null)
          starting_phase.drop_objection(this);
    endtask

    `uvm_object_utils(case1_sequence)
endclass

// 並增加一個 case1 的 base_test
class my_case1 extends base_test;

  function new(string name = "my_case1", uvm_component parent = null);
    super.new(name, parent);
    `uvm_info("my_case1", "my_case1 is new", UVM_LOW);
  endfunction

  extern virtual function void build_phase(uvm_phase phase);

  `uvm_component_utils(my_case1)

endclass


function void my_case1::build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          case1_sequence::type_id::get());
endfunction
