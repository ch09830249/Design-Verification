class my_driver extends uvm_driver#(my_transaction);
    virtual my_if vif;

    `uvm_component_utils(my_driver)
    function new(string name = "my_driver", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("my_driver", "new is called", UVM_LOW);
    endfunction

    extern virtual task main_phase(uvm_phase phase);
    extern virutal task drive_one_pkt(my_transaction tr);

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("my_driver", "build_phase is called", UVM_LOW);
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif)) 
            `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
    endfunction
endclass

// 當把二者連接好之後，就可以在 driver 中透過 get_next_item 任務向 sequencer 申請新的 transaction
task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this);
    vif.data <= 8'b0;
    vif.valid <= 1'b0;
    while(!vif.rst_n)
        @(posedge vif.clk);
    /*
        while（1）循環因為 driver 只負責驅動 transaction，而不負責產生，只要有 transaction 就驅動，
        所以必須做成一個無限循環的形式。這與 monitor、reference model 和 scoreboard 的情況非常類似。
    */
    while(1) begin
        // req = new("req");
        // assert(req.randomize() with {pload.size == 200;});
        seq_item_port.get_next_item(req);   // 透過 get_next_item 任務來得到一個新的 req
        drive_one_pkt(req);                 // 並且驅動它
        seq_item_port.item_done();          
        /* 
            驅動完成後呼叫 item_done 通知 sequencer (當 driver 使用 get_next_item 得到一個 transaction 時，sequencer 自己也保留一份剛剛發送的 transaction
            當出現 sequencer 發出了 transaction，而 driver 並沒有得到的情況時，sequencer 會把保留的這份 transaction 再送出去。
            那麼 sequencer 如何知道 driver 是否已經成功得到 transaction 呢？如果在下次調用 get_next_item 前，item_done 被調用，那麼 sequencer 就認為 driver 已經得到了這個 transaction
            ，將會刪除這個 transaction。換言之，這其實是為了增加可靠性而使用的握手機制 
            在 sequence 中，向 sequencer 發送 transaction 使用的是 uvm_do巨集。這個巨集什麼時候會回傳呢？ uvm_do 宏產生了一個 transaction 並交給 sequencer，
            driver 取走這個 transaction 後，uvm_do 並不會立刻返回執行下一次的 uvm_do 宏，而是等待在那裡，直到 driver 返回 item_done 訊號。
            此時，uvm_do 宏才算是執行完畢，返回後開始執行下一個 uvm_do，並產生新的 transaction。
        */

        /*
            除 get_next_item 之外，還可以使用 try_next_item。 get_next_item 是阻塞的，它會一直等到有新的 transaction 才會回傳；
            try_next_item 則是非阻塞的，它嘗試著詢問 sequencer 是否有新的 transaction，如果有，則得到此 transaction，否則就直接回傳。
            所以可以改成
            while(1) begin
                seq_item_port.try_next_item(req);
                if(req == null)
                    @(posedge vif.clk);
                else begin
                    drive_one_pkt(req);
                    seq_item_port.item_done();
                end
            end
            相較於 get_next_item，try_next_item 的行為更接近真實 driver 的行為：當有數據時，就驅動數據，否則總線將一直處於空閒狀態。
        */
    end
    repeat(5) @(posedge vif.clk);
    phase.drop_objection(this);
endtask

task my_driver::drive_one_pkt(my_transaction tr);
    bit [47:0] tmp_data;
    bit [7:0] data_q[$];

    data_size = tr.pack_bytes(data_q) / 8;

    `uvm_info("my_driver", "begin to drive one pkt", UVM_LOW);
    repeat(3) @(posedge vif.clk);

    while (data_q.size() > 0) begin
        @(posedge vif.clk);
        vif.valid <= 1'b1;
        vif.data <= data_q.pop_front();
    end

    @(posedge vif.clk);
    vif.valid <= 1'b0;
    `uvm_info("my_driver", "end drive one pkt", UVM_LOW);
endtask