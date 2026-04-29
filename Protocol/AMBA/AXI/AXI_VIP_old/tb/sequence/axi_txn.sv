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

    constraint c_basic {
        // ----------------------
        // burst_type 合法值
        // ----------------------
        burst_type inside {2'b00, 2'b01, 2'b10}; // FIXED, INCR, WRAP
        // ----------------------
        // burst_len（AXI: 0~255 代表 1~256 beats）
        // 常用幾種長度
        // ----------------------
        burst_len inside {0, 3, 7, 15}; // 對應 1,4,8,16 beats
        // ----------------------
        // burst_size（每 beat bytes = 2^size）
        // 假設 32-bit bus → 最大 4 bytes → size=2
        // ----------------------
        burst_size inside {[0:2]}; // 1B,2B,4B
        // ----------------------
        // 地址對齊（非常重要）
        // ----------------------
        addr % (1 << burst_size) == 0;
        // ----------------------
        // qos 範圍
        // ----------------------
        qos inside {[0:15]};
        // ----------------------
        // lock（簡化）
        // ----------------------
        lock inside {0, 1};
        // ----------------------
        // wstrb（byte enable）
        // 32-bit → 4 bit
        // ----------------------
        wstrb inside {[1:15]}; // 避免全 0
    }

    constraint c_rw {
        // write → 必須有 data
        if (is_write) {
            data.size() == burst_len + 1;
        }
        // read → 不需要 data（或設為 0）
        if (!is_write) {
            data.size() == 0;
        }
    }

    constraint c_wrap {
        if (burst_type == 2'b10) { // WRAP
            // burst_len 必須是 2^N - 1（AXI 規範）
            burst_len inside {1, 3, 7, 15};

            // 地址需對齊整個 burst boundary
            addr % ((burst_len + 1) * (1 << burst_size)) == 0;
        }
    }

    constraint c_data {
        foreach (data[i]) {
            data[i] inside {[32'h0 : 32'hFFFF_FFFF]};
        }
    }

    // constraint c_distribution {
    //     // burst type 平衡
    //     burst_type dist {
    //         2'b00 := 1, // FIXED
    //         2'b01 := 3, // INCR（多一點）
    //         2'b10 := 1  // WRAP
    //     };

    //     // burst_len 常見值多跑
    //     burst_len dist {
    //         0  := 2,  // 1 beat
    //         3  := 3,  // 4 beats
    //         7  := 3,  // 8 beats
    //         15 := 2   // 16 beats
    //     };

    //     // qos corner case
    //     qos dist {
    //         0  := 2,
    //         15 := 2,
    //         [1:14] := 6
    //     };
    // }

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
