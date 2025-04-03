class my_monitor extends uvm_monitor;

    virtual my_if vif;

    // 在 UVM 的 transaction 層級的通訊中，資料的發送有多種方式，其中一種是使用 uvm_analysis_port
    // uvm_analysis_port 是一個參數化的類，其參數就是這個 analysis_port 所需要傳遞的資料的型別
    uvm_analysis_port #(my_transaction) ap;     // 建立 handle

    `uvm_component_utils(my_monitor)

    function new(string name = "my_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
            `uvm_fatal("my_monitor", "virtual interface must be set for vif!!!")
        ap = new("ap", this);                   // 實例化端口
    endfunction

    extern task main_phase(uvm_phase phase);
    extern task collect_one_pkt(my_transaction tr);

endclass

task my_monitor::main_phase(uvm_phase phase);
    my_transaction tr;
    while (1) begin
        tr = new("tr");
        collect_one_pkt(tr);
        // 在 main_phase 中，收集完一個 transaction 後，需要將其寫入 ap 中
        ap.write(tr);       // write 是 uvm_analysis_port 的一個內建函數
    end
endtask

task my_monitor::collect_one_pkt(my_transaction tr);
    bit[7:0] data_q[$];
    int psize;

    while (1) begin
        @(posedge vif.clk);
        if (vif.valid) break;
    end

    `uvm_info("my_monitor", "begin to collect one pkt", UVM_LOW);

    while (vif.valid) begin
        data_q.push_back(vif.data);
        @(posedge vif.clk);
    end

    // Pop dmac
    for (int i = 0; i < 6; i++) begin
        tr.dmac = {tr.dmac[39:0], data_q.pop_front()};
    end

    // Pop smac
    …

    // Pop ether_type
    …

    // Pop payload
    …

    // Pop crc
    for (int i = 0; i < 4; i++) begin
        tr.crc = {tr.crc[23:0], data_q.pop_front()};
    end

    `uvm_info("my_monitor", "end collect one pkt, print it:", UVM_LOW);
    tr.my_print();
endtask