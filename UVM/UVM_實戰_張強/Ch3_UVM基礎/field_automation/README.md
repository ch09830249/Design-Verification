# field automation 機制相關的宏
## 基本型別
```
`define uvm_field_int(ARG,FLAG)
`define uvm_field_real(ARG,FLAG)
`define uvm_field_enum(T,ARG,FLAG)
`define uvm_field_object(ARG,FLAG)
`define uvm_field_event(ARG,FLAG)
`define uvm_field_string(ARG,FLAG)
```
* 上述幾個巨集分別用於要註冊的欄位是整數、實數、枚舉型別、直接或間接衍生自 uvm_object 的型別、事件及字串型別。
* 對於枚舉型別來說，需要有三個參數。假如有枚舉類型 tb_bool_e，同時有變數 tb_flag，那麼在使用 field automation 機制時應該使用以下方式實作：
```
typedef enum {TB_TRUE, TB_FALSE} tb_bool_e;
…
tb_bool_e tb_flag;
…
`uvm_field_enum(tb_bool_e, tb_flag, UVM_ALL_ON)
```
## 動態數組型別
```
`define uvm_field_array_enum(ARG,FLAG)
`define uvm_field_array_int(ARG,FLAG)
`define uvm_field_array_object(ARG,FLAG)
`define uvm_field_array_string(ARG,FLAG)
```
PS: 相較於前面的 uvm_field 系列巨集少了 event 型別和 real 型別。另外一個重要的變化是 enum 類型的陣列裡也只有兩個參數
## 靜態數組型別
```
`define uvm_field_sarray_int(ARG,FLAG)
`define uvm_field_sarray_enum(ARG,FLAG)
`define uvm_field_sarray_object(ARG,FLAG)
`define uvm_field_sarray_string(ARG,FLAG)
```
## 隊列相關
```
`define uvm_field_queue_enum(ARG,FLAG)
`define uvm_field_queue_int(ARG,FLAG)
`define uvm_field_queue_object(ARG,FLAG)
`define uvm_field_queue_string(ARG,FLAG)
```
PS: 對於 enum 類型來說，也只需要兩個參數
## 聯合數組相關
```
`define uvm_field_aa_int_string(ARG, FLAG)
`define uvm_field_aa_string_string(ARG, FLAG)
`define uvm_field_aa_object_string(ARG, FLAG)
`define uvm_field_aa_int_int(ARG, FLAG)
`define uvm_field_aa_int_int_unsigned(ARG, FLAG)
`define uvm_field_aa_int_integer(ARG, FLAG)
`define uvm_field_aa_int_integer_unsigned(ARG, FLAG)
`define uvm_field_aa_int_byte(ARG, FLAG)
`define uvm_field_aa_int_byte_unsigned(ARG, FLAG)
`define uvm_field_aa_int_shortint(ARG, FLAG)
`define uvm_field_aa_int_shortint_unsigned(ARG, FLAG)
`define uvm_field_aa_int_longint(ARG, FLAG)
`define uvm_field_aa_int_longint_unsigned(ARG, FLAG)
`define uvm_field_aa_string_int(ARG, FLAG)
`define uvm_field_aa_object_int(ARG, FLAG)
```
* 聯合數組有兩大識別標誌，一是索引的類型，二是儲存資料的類型
* 在這一系列 uvm_field 系列巨集中，出現的**第一個類型是儲存資料類型，第二個類型是索引類型**
  * 如 uvm_field_aa_int_string 用於聲明那些儲存的資料是 int，而其索引是 string 類型的聯合數組
# field automation 機制的常用函數
* **copy 函數用於實例的複製**
  * 如果要把某個 A 實例複製到 B 實例中，那麼應該使用 B.copy（A）
  * 在使用此函數前，B 實例必須已經使用 new 函數分配好了內存空間
```
extern function void copy (uvm_object rhs);
```
* **compare 函數用來比較兩個實例是否一樣**
  * 如果要比較 A 與 B 是否一樣，可以使用 A.compare（B），也可以使用 B.compare（A）
  * 當兩者一致時，返回1；否則為0
```
extern function bit compare (uvm_object rhs, uvm_comparer comparer=null);
```
* **pack_bytes 函數用於將所有的欄位打包成 byte 流**
```
extern function int pack_bytes (ref byte unsigned bytestream[], input uvm_packer packer=null);
```
* **unpack_bytes 函數用來將一個byte流逐一恢復到某個類別的實例中**
```
extern function int unpack_bytes (ref byte unsigned bytestream[], input uvm_packer packer=null);
```
* **pack 函數用於將所有的字段打包成 bit 流**
```
extern function int pack (ref bit bitstream[], input uvm_packer packer=null);
```
* **unpack 函數用於將一個 bit 流逐一恢復到某個類別的實例中**
```
extern function int unpack (ref bit bitstream[], input uvm_packer packer=null);
```
* **pack_ints 函數用來將所有的欄位打包成 int（4 個 byte，或是 dword）流**
```
extern function int pack_ints (ref int unsigned intstream[], input uvm_packer packer=null);
```
* **unpack_ints 函數用來將一個 int 流逐一恢復到某個類別的實例中**
```
extern function int unpack_ints (ref int unsigned intstream[], input uvm_packer packer=null);
```
* **print 函數用於列印所有的字段**
* **clone 函數前面有介紹**
```
extern virtual function uvm_object clone ();
```
# field automation 機制中標誌位的使用
```
//A=ABSTRACT Y=PHYSICAL
//F=REFERENCE, S=SHALLOW, D=DEEP
//K=PACK, R=RECORD, P=PRINT, M=COMPARE, C=COPY
//--------------------------- AYFSD K R P M C
parameter UVM_ALL_ON = 'b000000101010101;
parameter UVM_COPY = (1<<0);
parameter UVM_NOCOPY = (1<<1);
parameter UVM_COMPARE = (1<<2);
parameter UVM_NOCOMPARE = (1<<3);
parameter UVM_PRINT = (1<<4);
parameter UVM_NOPRINT = (1<<5);
parameter UVM_RECORD = (1<<6);
parameter UVM_NORECORD = (1<<7);
parameter UVM_PACK = (1<<8);
parameter UVM_NOPACK = (1<<9);
```
* UVM_ALL_ON 的值是’b000000101010101，表示開啟 copy、compare、print、record、pack 功能
## Example
考慮實現這樣一種功能：給 DUT 施加一種 CRC 錯誤的異常激勵。實作這個功能的一種方法是在 my_transaction 中加入一個 crc_err 的標誌位：
```
class my_transaction extends uvm_sequence_item;

  rand bit[47:0] dmac;
  rand bit[47:0] smac;
  rand bit[15:0] ether_type;
  rand byte pload[];
  rand bit[31:0] crc;
  rand bit crc_err;  // 但是這個 bit 不應該包入 transaction
  …

  function void post_randomize();
    if(crc_err)
      ; // do nothing
    else
      crc = calc_crc;
  endfunction

  …

endclass
```
**Q:** 對於多出來的這個字段，是不是也應該用 uvm_field_int 巨集來註冊呢？如果不使用巨集註冊的話，那麼當呼叫 print 函數時，在顯示結果中就看不到其值，但是如果使用了宏，結果就是這個根本就不需要在 pack 和 unpack 操作中出現的欄位出現了  
**A:** 在後面的控制域中加入 UVM_NOPACK 的形式來實現
```
`uvm_object_utils_begin(my_transaction)
  `uvm_field_int(dmac, UVM_ALL_ON)
  `uvm_field_int(smac, UVM_ALL_ON)
  `uvm_field_int(ether_type, UVM_ALL_ON)
  `uvm_field_array_int(pload, UVM_ALL_ON)
  `uvm_field_int(crc, UVM_ALL_ON)
  `uvm_field_int(crc_err, UVM_ALL_ON | UVM_NOPACK)
`uvm_object_utils_end
```
* **UVM_ALL_ON|UVM_NOPACK 的結果就是 ‘b000001101010101。這樣 UVM 在執行 pack 操作時，先檢查 bit9，發現其為 1，直接忽略 bit8 所代表的 UVM_PACK**
# field automation 中宏與 if 的結合
在乙太網路中，有一種幀是 VLAN 幀，這種幀是在普通乙太網路幀基礎上擴展而來的。而且並不是所有的乙太網路幀都是 VLAN 幀，如果一個幀是 VLAN 幀，那麼其中就會有 vlan_id 等字段（具體可以詳見乙太網路的相關協定），否則不會有這些欄位。**類似 vlan_id 等字段是屬於幀結構的一部分，但是這個字段可能有，也可能沒有**。由於讀者已經習慣了使用 uvm_field 系列巨集來進行 pack 和 unpack 操作，那麼很直觀的想法是使用動態數組的形式來實現：
```
class my_transaction extends uvm_sequence_item;
      rand bit[47:0] smac;
      rand bit[47:0] dmac;
      rand bit[31:0] vlan[];
      rand bit[15:0] eth_type;
      rand byte pload[];
      rand bit[31:0] crc;
      `uvm_object_utils_begin(my_transaction)
          `uvm_field_int(smac, UVM_ALL_ON)
          `uvm_field_int(dmac, UVM_ALL_ON)
          `uvm_field_array_int(vlan, UVM_ALL_ON)   // 這是可有可無的
          `uvm_field_int(eth_type, UVM_ALL_ON)
          `uvm_field_array_int(pload, UVM_ALL_ON)
      `uvm_object_utils_end
endclass
```
在隨機化普通乙太網路幀時，可以使用如下的方式：**(不需要 VLAN)**
```
my_transaction tr;
tr = new();
assert(tr.randomize() with {vlan.size() == 0;});
```
協定中規定 vlan 的欄位固定為 4 個位元組，所以在隨機化 VLAN 訊框時，可以使用如下的方式：**(有 VLAN )**
```
my_transaction tr;
tr = new();
assert(tr.randomize() with {vlan.size() == 1;});
```
**協定中規定 vlan 的 4 個位元組各自有其不同的意義**，這 4 個位元組分別代表 4 個不同的欄位。如果使用上面的方式，問題雖然解決了，但是這 4 個字段的意思不太明確。
一個可行的解決方案是：
```
class my_transaction extends uvm_sequence_item;

  rand bit[47:0] dmac;
  rand bit[47:0] smac;
  rand bit[15:0] vlan_info1;
  rand bit[2:0]  vlan_info2;
  rand bit       vlan_info3;
  rand bit[11:0] vlan_info4;
  rand bit[15:0] ether_type;
  rand byte      pload[];
  rand bit[31:0] crc;

  rand bit is_vlan;
 ...
  `uvm_object_utils_begin(my_transaction)
    `uvm_field_int(dmac, UVM_ALL_ON)
    `uvm_field_int(smac, UVM_ALL_ON)
    if (is_vlan) begin         // 根據 is_vlan 決定這些 field 是否要註冊
      `uvm_field_int(vlan_info1, UVM_ALL_ON)
      `uvm_field_int(vlan_info2, UVM_ALL_ON)
      `uvm_field_int(vlan_info3, UVM_ALL_ON)
      `uvm_field_int(vlan_info4, UVM_ALL_ON)
    end
    `uvm_field_int(ether_type, UVM_ALL_ON)
    `uvm_field_array_int(pload, UVM_ALL_ON)
    `uvm_field_int(crc, UVM_ALL_ON | UVM_NOPACK)
    `uvm_field_int(is_vlan, UVM_ALL_ON | UVM_NOPACK)
  `uvm_object_utils_end
 ...
endclass
```
在隨機化普通乙太網路幀時，可以使用如下的方式：**(不需要 VLAN)**
```
my_transaction tr;
tr = new();
assert(tr.randomize() with {is_vlan == 0;});     // 有個 flag 去控制
```
協定中規定 vlan 的欄位固定為 4 個位元組，所以在隨機化 VLAN 訊框時，可以使用如下的方式：**(有 VLAN )**
```
my_transaction tr;
tr = new();
assert(tr.randomize() with {is_vlan == 1;});
```
使用這種方式的 VLAN 幀，在執行 print 操作時，4 個字段的資訊將會非常明顯；在呼叫 compare 函數時，如果兩個 transaction 不同，將會更明確地指明是哪個欄位不一樣。
