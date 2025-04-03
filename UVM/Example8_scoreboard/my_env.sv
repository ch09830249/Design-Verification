class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;
    my_model mdl;
    // 建立 scoreboard handle
    my_scoreboard scb;
    uvm_tlm_analysis_fifo #(my_transaction) agt_mdl_fifo;
    // 建立 fifo for mdl => scb 的 handle
    uvm_tlm_analysis_fifo #(my_transaction) mdl_scb_fifo;
    // 建立 fifo for o_agt => scb 的 handle
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
        // 實例化 scoreboard
        scb   = my_model::type_id::create("scb", this);
        agt_mdl_fifo = new("agt_mdl_fifo", this);
        // 實例化 fifo
        mdl_scb_fifo = new("mdl_scb_fifo", this);
        agt_scb_fifo = new("agt_scb_fifo", this);
    endfunction

    function void my_env::connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        i_agt.ap.connect(agt_mdl_fifo.analysis_export);
        mdl.port.connect(agt_mdl_fifo.blocking_get_export);
        // 連接 mdl => scb
        mdl.ap.connect(mdl_scb_fifo.analysis_export);
        scb.exp_port.connect(mdl_scb_fifo.blocking_get_export); // reference model 為 expected value
        // 連接 o_agt => scb
        o_agt.ap.connect(agt_scb_fifo.analysis_export);
        scb.act_port.connect(agt_scb_fifo.blocking_get_export); // DUT 輸出 (actual value)
    endfunction

    `uvm_component_utils(my_env)
endclass