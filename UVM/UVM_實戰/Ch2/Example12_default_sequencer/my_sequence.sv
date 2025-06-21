/*
    使用 default_sequence 啟動 sequence 的方式取代了上一節程式碼清單2-66中在 sequencer 的 main_phase 中手動啟動 sequence 的相關語
    句，但是新的問題出現了：在上一節啟動 sequence 前後，分別提起和撤銷 objection，此時使用 default_sequence 又如何提起和撤銷
    objection呢？
*/
/*
    在 uvm_sequence 這個基底類別中，有一個變數名為 starting_phase，它的型別是 uvm_phase，sequencer 在啟動 default_sequence 時，會
    自動做如下相關操作：
        task my_sequencer::main_phase(uvm_phase phase);
            …
            seq.starting_phase = phase;
            seq.start(this);
            …
        endtask
*/
class my_sequence extends uvm_sequence #(my_transaction);
    my_transaction m_trans;

    function new(string name = "my_sequence");
        super.new(name);
    endfunction

    virtual task body();
        // 因此，可以在 sequence 中使用 starting_phase 進行提起和撤銷 objection
        if(starting_phase != null)
            starting_phase.raise_objection(this);
        repeat (10) begin
            `uvm_do(m_trans)
        end
        #1000;
        if(starting_phase != null)
            starting_phase.drop_objection(this);
        // 從而，objection 完全與 sequence 關聯在了一起，在其他任何地方都不必再設定 objection
    endtask

    `uvm_object_utils(my_sequence)
endclass