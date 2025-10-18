class axi_sequencer extends uvm_sequencer #(axi_txn);
    `uvm_component_utils(axi_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
