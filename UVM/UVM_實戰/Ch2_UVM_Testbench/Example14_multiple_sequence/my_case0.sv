class case0_sequence extends uvm_sequence #(my_transaction);
    my_transaction m_trans;

    function new(string name = "my_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info("my_case0", "my_case0's my_sequence", UVM_LOW);
        if(starting_phase != null)
            starting_phase.raise_objection(this);
        repeat (10) begin
            `uvm_do(m_trans)
        end
        #100;       // case0 #1000 => #100       
        if(starting_phase != null)
            starting_phase.drop_objection(this);
    endtask

    `uvm_object_utils(case0_sequence)
endclass

// 並增加一個 case0 的 base_test
class my_case0 extends base_test;

  function new(string name = "my_case0", uvm_component parent = null);
    super.new(name, parent);
    `uvm_info("my_case0", "my_case0 is new", UVM_LOW);
  endfunction

  extern virtual function void build_phase(uvm_phase phase);

  `uvm_component_utils(my_case0)

endclass

function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          case0_sequence::type_id::get());
endfunction
