class tlul_put_sequencer extends uvm_sequencer #(tlul_transaction);
  `uvm_component_utils(tlul_put_sequencer)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
