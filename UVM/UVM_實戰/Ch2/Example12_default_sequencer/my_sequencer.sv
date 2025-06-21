/*
    在上一節的例子中，
    sequence 是在 my_env 或是在 my_sequencer 的 main_phase 中手動啟動的，但是在實際應用中，
    使用最多的還是透過 default_sequence 的方式啟動 sequence。
*/
class my_sequencer extends uvm_sequencer #(my_transaction);

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    task my_sequencer::main_phase(uvm_phase phase);
        // my_sequence seq;
        // phase.raise_objection(this);
        // seq = my_sequence::type_id::create("seq");   // 手動啟動的部分
        // seq.start(this);
        // phase.drop_objection(this);
    endtask

    `uvm_component_utils(my_sequencer)
endclass