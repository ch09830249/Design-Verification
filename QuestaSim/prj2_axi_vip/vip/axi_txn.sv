// 封裝 AXI4 的基本傳輸內容，包括讀寫指令、burst 長度等
class axi_txn extends uvm_sequence_item;

    rand bit [3:0]           id;
    rand bit [31:0]          addr;
    rand bit [31:0]          data[$]; // 支援 burst 資料
    rand bit [7:0]           burst_len;
    rand bit [2:0]           burst_size;
    rand bit [1:0]           burst_type;
    rand bit                 is_write;
    rand bit                 lock;
    rand bit [3:0]           qos;

    `uvm_object_utils(axi_txn)

    function new(string name = "axi_txn");
        super.new(name);
    endfunction

    function void do_print(uvm_printer printer);
        super.do_print(printer);
        printer.print_field_int("id", id, 4);
        printer.print_field_int("addr", addr, 32);
        printer.print_field_int("burst_len", burst_len, 8);
        printer.print_field_int("burst_size", burst_size, 3);
        printer.print_field_int("burst_type", burst_type, 2);
        printer.print_field_int("lock", lock, 1);
        printer.print_field_int("qos", qos, 4);
        printer.print_field_int("is_write", is_write, 1);
        foreach (data[i])
            printer.print_field_int($sformatf("data[%0d]", i), data[i], 32);
    endfunction

endclass
