class axi_write_env extends uvm_env;

  `uvm_component_utils(axi_write_env)

  axi_write_agent write_agent;

  function new(string name = "axi_write_env", uvm_component parent = null);  
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    write_agent = axi_write_agent::type_id::create("write_agent", this);
  endfunction
endclass
