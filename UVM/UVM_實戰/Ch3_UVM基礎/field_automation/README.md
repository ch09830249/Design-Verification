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
這裡一共出現了15種。聯合數組有兩大識別標誌，一是索引的類型，二是儲存資料的類型。在這一系列uvm_field系列巨集中，
出現的第一個類型是儲存資料類型，第二個類型是索引類型，如uvm_field_aa_int_string用於聲明那些儲存的資料是int，而其索引
是string類型的聯合數組。
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
# field automation 中宏與 if 的結合
