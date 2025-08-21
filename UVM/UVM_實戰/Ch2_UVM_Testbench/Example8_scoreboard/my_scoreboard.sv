class my_scoreboard extends uvm_scoreboard;
    my_transaction expect_queue[$];
    // my_scoreboard 要比較的資料一是來自 reference model，二是來自 o_agt 的 monitor。前者透過 exp_port 獲取，而後者透過 act_port 獲取
    uvm_blocking_get_port #(my_transaction) exp_port;
    uvm_blocking_get_port #(my_transaction) act_port;

    `uvm_component_utils(my_scoreboard)

    extern function new(string name, uvm_component parent = null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual task main_phase(uvm_phase phase);
endclass

function my_scoreboard::new(string name, uvm_component parent = null);
    super.new(name, parent);
endfunction

function void my_scoreboard::build_phase(uvm_phase phase);
    super.build_phase(phase);
    // new 兩個 port
    exp_port = new("exp_port", this);
    act_port = new("act_port", this);
endfunction

task my_scoreboard::main_phase(uvm_phase phase);
    my_transaction get_expect, get_actual, tmp_tran;
    bit result;
    phase.raise_objection(this);    // 加 objection, 收到來自 model 的 tr 和 monitor 的 tr 並比對
    super.main_phase(phase);
    // 在 main_phase 中透過 fork 建立起了 2 個進程
    fork
        // 一個進程處理 exp_port 的數據，當收到數據後，把數據放入 expect_queue 中
        while (1) begin
            exp_port.get(get_expect);
            expect_queue.push_back(get_expect);     // 塞該 tr 進 queue
            break;
        end
        /*
            另外一個進程處理 act_port 的數據，這是 DUT 的輸出數據，當收集到這些數據後，從 expect_queue 中彈出之前從 exp_port 收到的數據，
            並調用 my_transaction 函數的 my_compare_transaction。
        */
        while (1) begin
            act_port.get(get_actual);
            if(expect_queue.size() > 0) begin
                tmp_tran = expect_queue.pop_front();
                result = get_actual.my_compare(tmp_tran);
                if(result) begin
                    `uvm_info("my_scoreboard", "Compare SUCCESSFULLY", UVM_LOW);
                end
                else begin
                    `uvm_error("my_scoreboard", "Compare FAILED");
                    $display("the expect pkt is");
                    tmp_tran.my_print("my_scoreboard");
                    $display("the actual pkt is");
                    get_actual.my_print("my_scoreboard");
                end
                break;      // 比對成功一筆 tr 就 break
            end
            else begin  
                /* 
                    Expect Queue 為空的, 採用這種比較處理方式的前提是 exp_port 要比 act_port 先收到數據。由於 DUT 處理資料需要延時，
                    而 reference model 是基於高階語言的處理，一般不需要延時，因此可以確保 exp_port 的資料在 act_port 的資料之前到來。
                */
                `uvm_error("my_scoreboard", "Received from DUT, while Expect Queue is empty");
                $display("the unexpected pkt is");
                get_actual.my_print("my_scoreboard");
            end
        end
    join
    phase.drop_objection(this);
endtask
