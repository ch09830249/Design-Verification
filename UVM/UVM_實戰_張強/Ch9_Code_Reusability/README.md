# UVM 中程式碼的可重複使用性
## 廣義的 callback 函數
在前文介紹 my_transaction 時，曾經在其 post_randomize 中呼叫 calc_crc 函式：
```
function void post_randomize();
  crc = calc_crc;
endfunction
```
my_transaction 的最後一個欄位是 CRC 校驗資訊。假如沒有 post_randomize()，那麼 CRC 必須在整個 transaction 的資料都固定之後才能計算出來。
```
my_transaction tr;
assert(tr.randomize());
tr.crc = tr.calc_crc();
```
執行前兩句之後，tr 中的 crc 欄位的值是一個隨機的值，要將其設定成真正反映這個 transaction 資料的 CRC 訊息，需要在
randoimize() 之後呼叫一個 calc_crc，calc_crc 是一個自訂的函數。
呼叫 calc_crc 的過程有點繁瑣，因為每次執行 randomize 函數之後都要調用一次，如果忘記調用，將很可能成為驗證平台的一個
隱患，非常隱蔽且不容易發現。期望有一種方法能夠在執行 randomize 函數之後自動呼叫 calc_crc 函數。 randomize 是 SystemVerilog 提
供的一個函數，同時 SystemVerilog 也提供了一個 post_randomize() 函數，當 randomize() 之後，系統會自動呼叫 post_randomize 
函數，像如上的三句話，執行時實際如下：
```
my_transaction tr;
assert(tr.randomize());
tr.post_randomize();
tr.crc=tr.calc_crc();
```
其中 tr.post_randomize 是自動呼叫的，所以如果能夠重載 post_randomize 函數，在其中執行 calc_crc 函數，那麼就可以達到目的
了：
```
function void my_transaction::post_randomize();
  super.post_randomize();
  crc=this.calc_crc();
endfunction
```
post_randomize 就是 SystemVerilog 提供的一個 callback 函數。這也是最簡單的 callback 函數。
 post_randomize 的例子似乎與本節引言中提到的 callback 機制不同，引言中強調兩個項目之間。不過如果將 SystemVerilog 語言的
開發過程作為一個專案 A，驗證人員使用 SystemVerilog 開發的是專案 B。 A 的開發者預料到 B 可能會在 randomize 函數完成後做一些
事情，於是 A 為 SystemVerilog 加入了 post_randomize 函數。 B 如 A 所料，使用了這個 callback 函數。
post_randomize 函數是 SystemVerilog 提供的廣義的 callback 函數。 UVM 也為使用者提供了廣義的 callback 函數/任務：pre_body 和
 post_body，除此之外還有 pre_do、mid_do 和 post_do。相信很多用戶已經從中受益了。
## UVM 中 callback 機制的原理
```
task my_driver::main_phase();
  …
  while(1) begin
    seq_item_port.get_next_item(req);
    pre_tran(req);
    …
  end
endtask
```
假設這是一個成熟的 VIP 中的 driver，那麼考慮如何實作 pre_tran 的 callback 函數/任務呢？它應該是 my_driver 的函數/任務。
如果按照上面 post_randomize 的經驗，那麼應該從 my_driver 衍生一個類別 new_driver，然後重寫 pre_tran 這個函數/任務。但這種想法
是行不通的，因為這是一個完整的 VIP，雖然從 my_driver 派生了 new_driver，但是這個 VIP 中正常運行時使用的依然是 my_driver，
而不是 new_driver。 new_driver 這個衍生類別根本就沒有實例化過，所以 pre_tran 從來不會運作。當然，這裡可以使用 factory 機制的重
載功能，但是那樣是 factory 機制的功能，而不是 callback 機制的功能，所以暫不考慮 factory 機制的重載功能。
為了解決這個問題，嘗試新引入一個類別：
