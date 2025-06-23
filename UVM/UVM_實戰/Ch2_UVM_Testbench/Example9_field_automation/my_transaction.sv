class my_transaction extends uvm_sequence_item;

    rand bit[47:0] dmac;
    rand bit[47:0] smac;
    rand bit[15:0] ether_type;
    rand byte pload[];
    rand bit[31:0] crc;

    constraint pload_cons {
        pload.size >= 46;
        pload.size <= 1500;
    }

    function bit[31:0] calc_crc();
        return 32'h0;
    endfunction

    function void post_randomize();
        crc = calc_crc;
    endfunction

    // `uvm_object_utils(my_transaction)

    /*
        使用 uvm_object_utils_begin 和 uvm_object_utils_end 來實作 my_transaction 的 factory 註冊，
        在這兩個宏中間，使用 uvm_field 巨集註冊所有字段。 uvm_field 系列巨集隨著 transaction 成員變數的不同而不同，

        使用上述巨集註冊之後，可以直接呼叫 copy、compare、print 等函數，而無需自己定義。這大大簡化了驗證平台的搭建，提高了效率
    */
    `uvm_object_utils_begin(my_transaction)
        `uvm_field_int(dmac, UVM_ALL_ON)            // 針對 bit 類型的 uvm_field_int
        `uvm_field_int(smac, UVM_ALL_ON)
        `uvm_field_int(ether_type, UVM_ALL_ON)
        `uvm_field_array_int(pload, UVM_ALL_ON)     // 針對 byte 型別動態陣列的 uvm_field_array_int
        `uvm_field_int(crc, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "my_transaction");
        super.new(name);
    endfunction

    // 以下 my_copy, my_compare, my_print 改透過 field automation 實作
    // function void my_print();
    //     $display("dmac = %0h", dmac);
    //     $display("smac = %0h", smac);
    //     $display("ether_type = %0h", ether_type);
    //     for(int i = 0; i < pload.size; i++) begin
    //         $display("pload[%0d] = %0h", i, pload[i]);
    //     end
    //     $display("crc = %0h", crc);
    // endfunction

    // function void my_copy(my_transaction tr);
    //     if(tr == null)
    //         `uvm_fatal("my_transaction", "tr is null!!!!")
    //     dmac = tr.dmac;
    //     smac = tr.smac;
    //     ether_type = tr.ether_type;
    //     pload = new[tr.pload.size()];
    //     for(int i = 0; i < pload.size(); i++) begin
    //         pload[i] = tr.pload[i];
    //     end
    //     crc = tr.crc;
    // endfunction

    // function bit my_compare(my_transaction tr);
    //     bit result;

    //     if(tr == null)
    //         `uvm_fatal("my_transaction", "tr is null!!!!")
    //     result = ((dmac == tr.dmac) &&
    //             (smac == tr.smac) &&
    //             (ether_type == tr.ether_type) &&
    //             (crc == tr.crc));
    //     if(pload.size() != tr.pload.size())
    //         result = 0;
    //     else
    //         for(int i = 0; i < pload.size(); i++) begin
    //             if(pload[i] != tr.pload[i])
    //                 result = 0;
    //         end
    //     return result;
    // endfunction
endclass