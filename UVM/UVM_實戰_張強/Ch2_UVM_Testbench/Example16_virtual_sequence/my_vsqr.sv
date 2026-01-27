class my_vsqr extends uvm_sequencer #(my_transaction);
    // 該 vsqr 須包含兩個 my_sequencer
    my_sequencer p_sqr0;
    my_sequencer p_sqr1;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    `uvm_component_utils(my_vsqr)
endclass
