class my_model extends uvm_component;
    /*
        UVM 的 transaction 層級通訊的資料接收方式也有多種，其中一種就是使用 uvm_blocking_get_port。這也是一個參數化的類，其參數是其中要傳遞的 transaction 的類型。
    */
    // 建立 handle 
    uvm_blocking_get_port #(my_transaction) port;       // 接收來自 monitor 的 tr
    uvm_analysis_port #(my_transaction) ap;             // 傳送 tr 給 scoreboard

    extern function new(string name, uvm_component parent);
    extern function void build_phase(uvm_phase phase);
    extern virtual task main_phase(uvm_phase phase);

    `uvm_component_utils(my_model)
endclass

function my_model::new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_info("my_model", "my_model is new", UVM_LOW);
endfunction

function void my_model::build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("my_model", "main_phase is called", UVM_LOW);
    // 實例化
    port = new("port", this);
    ap = new("ap", this);
endfunction

/*
    在 my_model 的 main_phase 中，只是單純地複製一份從 i_agt 得到的 tr，並傳遞給後級的 scoreboard 中。
*/
task my_model::main_phase(uvm_phase phase);
    my_transaction tr;
    my_transaction new_tr;
    super.main_phase(phase);
    while(1) begin
        port.get(tr);               // 透過該 port 取出 tr (env 的 fifo 中取 tr)
        new_tr = new("new_tr");     // new 一個新 tr
        new_tr.my_copy(tr);         // 複製一份
        `uvm_info("my_model", "get one transaction, copy and print it:", UVM_LOW)
        new_tr.my_print("my_model");
        ap.write(new_tr);           // 傳給 scoreboard
        break;                      // 這裡收到一筆就 break
    end
endtask
