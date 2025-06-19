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

        /*
            這裡 set 函數的第一個參數由 null 變成了 this，而第二個代表路徑的參數則去除了 uvm_test_top。
            第二個參數是相對於第一個參數的相對路徑，由於上述程式碼是在 my_env 中，而 my_env 本身已經是uvm_test_top了，
            而第一個參數被設定為了 this，所以第二個參數中就不需要 uvm_test_top了。
            在 top_tb 中設定 virtual interface 時，由於 top_tb 不是一個類，無法使用 this 指針，所以設定 set 的第一個參數為 null
            第二個參數使用 uvm_test_top.XXX
        */
        /*
            在第二個路徑參數中，出現了 main_phase。這是 UVM 在設定 default_sequence 時的要求。由於除了 main_phase 外，還有其他任務 phase，
            例如 configure_phase、reset_phase 等，所以必須指定是哪個 phase，讓 sequencer 知道在哪個 phase 啟動這個 sequence。
        */
        // 由於UVM的規定，使用者在使用時照做即可。
        uvm_config_db#(uvm_object_wrapper)::set(this,
                                                "i_agt.sqr.main_phase",     
                                                "default_sequence",
                                                my_sequence::type_id::get());

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

    `uvm_component_utils(my_env)
endclass