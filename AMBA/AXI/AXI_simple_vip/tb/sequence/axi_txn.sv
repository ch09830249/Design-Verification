// 封裝 AXI4 的基本傳輸內容，包括讀寫指令、burst 長度等
class axi_txn extends uvm_sequence_item;

    rand bit [3:0]           id;
    rand bit [31:0]          addr;
    rand bit [31:0]          data[$];       // 支援 burst 資料
    rand bit [7:0]           burst_len;
    rand bit [2:0]           burst_size;
    rand bit [1:0]           burst_type;
    rand bit                 is_write;
    rand bit                 lock;
    rand bit [3:0]           qos;
    rand bit [3:0]           wstrb;

    `uvm_object_utils_begin(axi_txn)
        `uvm_field_int(id, UVM_DEFAULT)
        `uvm_field_int(addr, UVM_DEFAULT)
        `uvm_field_queue_int(data, UVM_DEFAULT)
        `uvm_field_int(burst_len, UVM_DEFAULT)
        `uvm_field_int(burst_size, UVM_DEFAULT)
        `uvm_field_int(burst_type, UVM_DEFAULT)
        `uvm_field_int(is_write, UVM_DEFAULT)
        `uvm_field_int(lock, UVM_DEFAULT)
        `uvm_field_int(qos, UVM_DEFAULT)
        `uvm_field_int(wstrb, UVM_DEFAULT)
    `uvm_object_utils_end

    function new(string name = "axi_txn");
        super.new(name);
    endfunction

endclass
