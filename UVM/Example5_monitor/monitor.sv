class my_monitor extends uvm_monitor;       // 所有的 monitor 類別應該衍生自 uvm_monitor

    virtual my_if vif;                      // 與 driver 類似，在 my_monitor 中也需要有一個 virtual my_if，這樣才能監聽 DUT

    `uvm_component_utils(my_monitor)        // uvm_monitor 在整個仿真中是一直存在的，所以它是一個 component，要使用 uvm_component_util 巨集註冊

    function new(string name = "my_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))              // 透過 db config 取的
            `uvm_fatal("my_monitor", "virtual interface must be set for vif!!!")
    endfunction

    extern task main_phase(uvm_phase phase);
    extern task collect_one_pkt(my_transaction tr);

endclass

task my_monitor::main_phase(uvm_phase phase);
    my_transaction tr;
    while (1) begin         // 由於 monitor 需要時時收集數據，永不停歇，所以在 main_phase 中使用 while（1）循環來實現這一目的
        tr = new("tr");     // 先準備好一個空的 transaction 物件
        collect_one_pkt(tr);
    end
endtask

task my_monitor::collect_one_pkt(my_transaction tr);
    bit[7:0] data_q[$];
    int psize;

    while (1) begin
        @(posedge vif.clk);
        if (vif.valid) break;   // 當 interface 中的 valid 為 1 才去收資料, 否則就是 monitor ports
    end

    `uvm_info("my_monitor", "begin to collect one pkt", UVM_LOW);   // 有了 valid data, 可以開始先收到暫存資料的 data_q

    // 先將所有 data 一個一個 byte 塞進 data_q, 直到 valid 為 0
    while (vif.valid) begin
        data_q.push_back(vif.data);
        @(posedge vif.clk);
    end

    // 再將 data_q 中的收集好的資料 parse 成 (dmac + smac + ether_type + payload + crc)
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

/*
    在查閱 collect_one_pkt 的程式碼時，可以與 my_driver 的 drv_one_pkt 比較來看，兩者代碼非常相似。當收集完一個 transaction 後，
    透過 my_print 函數將其列印出來。 my_print 在 my_transaction
*/