class my_monitor extends uvm_monitor;
    virtual my_if vif;
    byte payload_q[$];
    uvm_analysis_port #(my_transaction) ap;

    `uvm_component_utils(my_monitor)

    function new(string name = "my_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
            `uvm_fatal("my_monitor", "virtual interface must be set for vif!!!")
        else
            `uvm_info("my_monitor", "get virtual interface vif successfully!!!", UVM_LOW);
        ap = new("ap", this);
    endfunction

    extern task main_phase(uvm_phase phase);
    extern task collect_one_pkt(my_transaction tr);

endclass

task my_monitor::main_phase(uvm_phase phase);
    my_transaction tr;
    `uvm_info("my_monitor", "main_phase is called", UVM_LOW);
    while (1) begin
        tr = new("tr");
        collect_one_pkt(tr);
        ap.write(tr);
    end
    `uvm_info("my_monitor", "main_phase is ended", UVM_LOW);
endtask

task my_monitor::collect_one_pkt(my_transaction tr);
    bit[7:0] data_q[$];
    int psize;
    int data_size;
    byte unsigned data_array[];

    while (1) begin
        @(posedge vif.clk);
        if (vif.valid) break;
    end

    `uvm_info("my_monitor", "begin to collect one pkt", UVM_LOW);

    while (vif.valid) begin
        data_q.push_back(vif.data);
        @(posedge vif.clk);
    end

    /*
        這裡使用 unpack_bytes 函數將 data_q 中的 byte 流轉換成 tr 中的各個欄位。 unpack_bytes 函數的輸入參數必須是一個動態數組，所
        以需要先把收集到的、放在 data_q 中的資料複製到一個動態陣列中。由於 tr 中的 pload 是一個動態數組，所以需要在調用
        unpack_bytes 之前就指定其大小，這樣 unpack_bytes 函數才能正常運作。
    */

    // 記錄收進來的 data size
    data_size = data_q.size();
    // new 一個 data array 暫存
    // unpack_bytes 函數的輸入參數必須是一個動態數組，所以需要先把收集到的、放在 data_q 中的資料複製到一個動態陣列中。
    data_array = new[data_size];
    for ( int i = 0; i < data_size; i++ ) begin
        data_array[i] = data_q[i];
    end
    // 由於 tr 中的 pload 是一個動態數組，所以需要在調用 unpack_bytes 之前就指定其大小，這樣 unpack_bytes 函數才能正常運作。
    tr.pload = new[data_size - 18]; //扣掉 da sa, e_type, crc
    // 直接 unpack 到該 transaction
    data_size = tr.unpack_bytes(data_array) / 8;

    // // Pop dmac
    // for (int i = 0; i < 6; i++) begin
    //     tr.dmac = {tr.dmac[39:0], data_q.pop_front()};
    // end

    // // Pop smac
    // for (int i = 0; i < 6; i++) begin
    //     tr.smac = {tr.smac[39:0], data_q.pop_front()};
    // end

    // // Pop ether_type
    // for (int i = 0; i < 2; i++) begin
    //     tr.ether_type = {tr.ether_type[7:0], data_q.pop_front()};
    // end

    // // Pop payload
    // payload_q = {};
    // for (int i = 0; i < 20; i++) begin
    //     payload_q.push_back(data_q.pop_front());
    // end
    // tr.pload = new[20];
    // for (int i = 0; i < payload_q.size(); i++) begin
    //     tr.pload[i] = payload_q[i];
    // end

    // // Pop crc
    // for (int i = 0; i < 4; i++) begin
    //     tr.crc = {tr.crc[23:0], data_q.pop_front()};
    // end

    `uvm_info("my_monitor", "end collect one pkt, print it:", UVM_LOW);
    // tr.my_print("my_monitor");
    tr.print();
endtask
