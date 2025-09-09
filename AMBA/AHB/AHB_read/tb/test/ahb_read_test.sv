class ahb_read_test extends uvm_test;
  `uvm_component_utils(ahb_read_test)

  ahb_read_env env;
  ahb_read_sequence seq;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    env = ahb_read_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    seq = ahb_read_sequence::type_id::create("seq");
    seq.start(env.agent.seqr);

    phase.drop_objection(this);
  endtask
endclass
