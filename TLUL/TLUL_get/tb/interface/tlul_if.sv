interface tlul_if(input logic clk, input logic rst_n);
  // Channel A — Request
  logic        a_valid;   // Master 發送請求時拉高。搭配 a_ready 表示有效交易。
  logic        a_ready;   // Slave 準備好接收請求時拉高。配合 a_valid 使用。
  logic [2:0]  a_opcode;  // 操作類型（opcode）。常見值：3'b000 = PutFullData（寫）3'b001 = PutPartialData 3'b100 = Get（讀）
  logic [2:0]  a_param;   // 根據 opcode 的附加參數。大多情況下設為 0（未使用）
  logic [3:0]  a_size;    // 表示資料大小（以 2 的次方為單位）。例：4'b010 = 4 bytes (word)
  logic [3:0]  a_mask;    // Byte mask。用來指定哪幾個 byte 是有效的（部分寫入時用）
  logic [31:0] a_address; // 請求的記憶體位址。需對齊 a_size
  logic [31:0] a_data;    // 寫入的資料（Put 操作才會使用）
  logic [2:0]  a_source;  // Source ID，辨識是哪一個 master 或交易發出者。可用於 response 對應。

  // Channel D — Response
  logic        d_valid;   // Slave 回傳回應時拉高。搭配 d_ready 表示回應有效。
  logic        d_ready;   // Master 準備好接收 response 時拉高。
  logic [2:0]  d_opcode;  // Response 類型。例：3'b000 = AccessAck 3'b001 = AccessAckData（含回傳資料）
  logic [2:0]  d_param;   // 與 d_opcode 搭配的參數。通常設為 0。
  logic [3:0]  d_size;    // 回應資料大小（與原請求相同）
  logic [31:0] d_data;    // 從 slave 讀出的資料（Get 對應的 response）
  logic [2:0]  d_source;  // 對應 A channel 的 a_source。用於回應對應哪一個請求。
  logic [1:0]  d_sink;    // Sink ID，用於管理 response buffer 等功能。對於簡單設計通常設為 0。
endinterface
