class my_sequencer extends uvm_sequencer #(my_transaction);

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    /*
        在 sequencer 中啟動與在 my_env 中啟動相比，唯一差異是 seq.start 的參數變成 this。
    */
    task my_sequencer::main_phase(uvm_phase phase);
        my_sequence seq;
        phase.raise_objection(this);
        seq = my_sequence::type_id::create("seq");
        seq.start(this);
        phase.drop_objection(this);
    endtask

    `uvm_component_utils(my_sequencer)
endclass