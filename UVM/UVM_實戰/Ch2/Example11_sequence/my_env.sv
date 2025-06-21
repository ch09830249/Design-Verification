class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;
    my_model mdl;
    my_scoreboard scb;
    uvm_tlm_analysis_fifo #(my_transaction) agt_mdl_fifo;
    uvm_tlm_analysis_fifo #(my_transaction) mdl_scb_fifo;
    uvm_tlm_analysis_fifo #(my_transaction) agt_scb_fifo;

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "i_agt", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "o_agt", "is_active", UVM_PASSIVE);
        i_agt = my_agent::type_id::create("i_agt", this);
        o_agt = my_agent::type_id::create("o_agt", this);
        mdl   = my_model::type_id::create("mdl", this);
        scb   = my_model::type_id::create("scb", this);
        agt_mdl_fifo = new("agt_mdl_fifo", this);
        mdl_scb_fifo = new("mdl_scb_fifo", this);
        agt_scb_fifo = new("agt_scb_fifo", this);
    endfunction

    function void my_env::connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        i_agt.ap.connect(agt_mdl_fifo.analysis_export);
        mdl.port.connect(agt_mdl_fifo.blocking_get_export);
        mdl.ap.connect(mdl_scb_fifo.analysis_export);
        scb.exp_port.connect(mdl_scb_fifo.blocking_get_export);
        o_agt.ap.connect(agt_scb_fifo.analysis_export);
        scb.act_port.connect(agt_scb_fifo.blocking_get_export);
    endfunction

    /*
        sequence 如何向 sequencer 中送出 transaction呢？
        只需要在某個 component（如 my_sequencer、my_env）的 main_phase 中啟動這個 sequence 即可
    */
    // 啟動 sequence 並且設定 sequence 將 transaction 送給哪個 sequencer (也可以在 sequencer 設定)
    // task my_env::main_phase(uvm_phase phase);
    //     my_sequence seq;
    //     phase.raise_objection(this);     // objection 一般伴隨著 sequence，通常只在 sequence 出現的地方才提起和撤銷 objection
    //     seq = my_sequence::type_id::create("seq");
    //     seq.start(i_agt.sqr);            // start 任務的參數是一個 sequencer 指針，如果不指明此指針，則 sequence 不知道將產生的 transaction 交給哪個 sequencer。
    //     phase.drop_objection(this);
    // endtask

    `uvm_component_utils(my_env)
endclass