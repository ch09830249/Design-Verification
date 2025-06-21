class my_driver extends uvm_driver;
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

task my_driver::main_phase(uvm_phase phase);
    my_transaction tr;
    ......
    for (int i = 0; i < 2; i++) begin
        tr = new("tr");
        assert(tr.randomize() with {pload.size == 200;});
        drive_one_pkt(tr);
    end
    ......
endtask

task my_driver::drive_one_pkt(my_transaction tr);
    bit [47:0] tmp_data;
    bit [7:0] data_q[$];

    /*
        第 42 行呼叫 pack_bytes 將 tr 中所有的欄位變成 byte 流放入 data_q 中，在2.3.1節中是手動地將所有欄位放入 data_q 中的。
        pack_bytes 大大減少了程式碼量。在把所有的欄位變成 byte 流放入 data_q 中時，欄位依照 uvm_field 系列巨集書寫的順序排列。
        是先放入 dmac，再依序放入 smac、ether_type、pload、crc。
        如果是以下 case
        `uvm_object_utils_begin(my_transaction)
            `uvm_field_int(smac, UVM_ALL_ON)
            `uvm_field_int(dmac, UVM_ALL_ON)
            `uvm_field_int(ether_type, UVM_ALL_ON)
            `uvm_field_array_int(pload, UVM_ALL_ON)
            `uvm_field_int(crc, UVM_ALL_ON)
        `uvm_object_utils_end
        那麼將會先放入smac，再依序放入dmac、ether_type、pload、crc。
    */
    data_size = tr.pack_bytes(data_q) / 8;

    // 以下將 packet 轉 Byte 資料流的 code 改成 field automation 方式實作
    // // Push dmac to data_q
    // tmp_data = tr.dmac;
    // for (int i = 0; i < 6; i++) begin
    //     data_q.push_back(tmp_data[7:0]);
    //     tmp_data = (tmp_data >> 8);
    // end

    // // Push smac to data_q
    // …

    // // Push ether_type to data_q
    // …

    // // Push payload to data_q
    // …

    // // Push crc to data_q
    // tmp_data = tr.crc;
    // for (int i = 0; i < 4; i++) begin
    //     data_q.push_back(tmp_data[7:0]);
    //     tmp_data = (tmp_data >> 8);
    // end

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