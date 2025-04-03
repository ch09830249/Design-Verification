class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;
    /*
        還需要在 my_env 中使用 fifo 將兩個端口聯繫在一起 (my_monitor 和 my_model 定義並實現了各自的連接埠要連接)。
    */
    // 建立 handle 
    uvm_tlm_analysis_fifo #(my_transaction) agt_mdl_fifo;   // fifo 的類型是 uvm_tlm_analysis_fifo，它本身也是一個參數化的類，其參數是儲存在其中的 transaction 的類型

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "i_agt", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "o_agt", "is_active", UVM_PASSIVE);
        i_agt = my_agent::type_id::create("i_agt", this);
        o_agt = my_agent::type_id::create("o_agt", this);
        // 在 my_env 中定義一個 fifo，並在 build_phase 中將其實例化
        agt_mdl_fifo = new("agt_mdl_fifo", this);
    endfunction

    // 在 connect_phase 中將 fifo 分別與 my_monitor 中的 analysis_port 和 my_model 中的 blocking_get_port相連
    function void my_env::connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        i_agt.ap.connect(agt_mdl_fifo.analysis_export);
        mdl.port.connect(agt_mdl_fifo.blocking_get_export);
    endfunction

    `uvm_component_utils(my_env)
endclass