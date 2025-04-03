class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;
    /*
        還需要在 my_env 中使用 fifo 將兩個端口聯繫在一起 (my_monitor 和 my_model 定義並實現了各自的連接埠要連接)。
    */
    // 建立 handle 
    my_model mdl;
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
        mdl   = my_model::type_id::create("mdl", this);     // 實例化 my_model
        // 在 my_env 中定義一個 fifo，並在 build_phase 中將其實例化
        agt_mdl_fifo = new("agt_mdl_fifo", this);
    endfunction

    /*
        這裡引入了 connect_phase。與 build_phase 及 main_phase 類似，connect_phase也是 UVM 內建的一個 phase，它在 build_phase 執行
        完成之後馬上執行。但是與 build_phase 不同的是，它的執行順序並不是從樹根到樹葉，而是從樹葉到樹根－先執行driver和 monitor 的 connect_phase，
        再執行 agent 的 connect_phase，最後執行 env 的 connect_phase。 (Bottom-Up)
    */
    function void my_env::connect_phase(uvm_phase phase);
        // 在 connect_phase 中將 fifo 分別與 my_monitor 中的 analysis_port 和 my_model 中的 blocking_get_port相連
        super.connect_phase(phase);
        /*
            不能直接把 my_monitor 中的 analysis_port 和 my_model 中的 blocking_get_port 連接嗎？由於
            analysis_port 是非阻塞性質的，ap.write 函數呼叫完成後馬上回傳，不會等待資料被接收。假如當 write 函數呼叫時，
            blocking_get_port 正在忙於其他事情，而沒有準備好接收新的資料時，此時被 write 函數寫入的 my_transaction 就需要一個暫存的位
            置，這就是 fifo。
        */
        i_agt.ap.connect(agt_mdl_fifo.analysis_export);         // 將 agent 中 monitor 的 ap 和 env 中的 fifo 相連
        mdl.port.connect(agt_mdl_fifo.blocking_get_export);     // 將 my_model 也和 env 中的 fifo 相連
    endfunction

    `uvm_component_utils(my_env)
endclass