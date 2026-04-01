class axi_read_test extends uvm_test;

  `uvm_component_utils(axi_read_test)

  axi_read_env env;

  function new(string name = "axi_read_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = axi_read_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    axi_read_sequence seq;
    phase.raise_objection(this);
    seq = axi_read_sequence::type_id::create("seq");
    seq.start(env.read_agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass
