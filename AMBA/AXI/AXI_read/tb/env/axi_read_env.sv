class axi_read_env extends uvm_env;

  `uvm_component_utils(axi_read_env)

  axi_read_agent read_agent;

  function new(string name = "axi_read_env", uvm_component parent = null);  
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    read_agent = axi_read_agent::type_id::create("read_agent", this);
  endfunction
endclass
