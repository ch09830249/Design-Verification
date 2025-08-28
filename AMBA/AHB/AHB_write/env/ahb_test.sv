class ahb_test extends uvm_test;
  `uvm_component_utils(ahb_test)

  ahb_env env;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    env = ahb_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    apb_write_sequence seq = apb_write_sequence::type_id::create("seq");
    seq.start(env.agent.driver.seq_item_port);
    phase.drop_objection(this);
  endtask
endclass
