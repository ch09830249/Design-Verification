# SVA
* SystemVerilog Assertions (SVA) 是 SystemVerilog 語言的一部分，專門用來**對設計的行為進行形式化的驗證和檢查**。它是一套功能強大且語意清楚的機制，可幫助硬體設計者和驗證工程師**在模擬、形式驗證中驗證時序與邏輯條件是否正確達成**。
* Assertion 被放在 verilog 設計中，方便在模擬時查看異常情況。當異常出現時，斷言會報警。一般在數位電路設計中都要加入斷言，斷言占整個設計的比例應不少於 30%。
# 立即斷言 Immediate Assertions
用來在模擬時「立即」檢查某個條件是否為真。這類斷言是在程式語句（例如 initial、always、task 或 function）中執行時就立即求值，不涉及時序或延遲行為。
## Immediate Assertion 的三種類型
| 類型       | 說明              | 主要用途     |
| -------- | --------------- | -------- |
| `assert` | 條件不成立時報錯        | 驗證條件是否正確 |
| `assume` | 假設條件成立（多用於形式驗證） | 限制環境條件   |
| `cover`  | 條件是否曾經成立過（覆蓋點）  | 蒐集覆蓋率    |
## 語法格式
```
assert (expression) [action_block];
assume (expression) [action_block];
cover  (expression) [action_block];
```
* expression：要檢查的條件。
* action_block：當條件不成立時要執行的動作（可選），通常是錯誤訊息或自定動作。
## 範例
1. assert：檢查條件，否則報錯
```
always @(posedge clk) begin
  assert (data_valid == 1'b1)
    else $fatal("錯誤：data_valid 沒有被拉高！");
end
```
2. assume：假設條件為真（形式驗證用）
```
always @(posedge clk) begin
  assume (reset_n == 1'b1);
end
```
3. cover：檢查條件是否曾經發生過
```
initial begin
  cover (start == 1'b1);
end
```
## 錯誤等級
| 等級   | 系統任務       | 說明                        |
| ---- | ---------- | ------------------------- |
| 致命錯誤 | `$fatal`   | 立即終止模擬。用於無法繼續模擬的重大錯誤。     |
| 錯誤   | `$error`   | 報告錯誤，不終止模擬。用於需關注的邏輯錯誤。    |
| 警告   | `$warning` | 報告警告，不會終止模擬。通常為非預期但非致命行為。 |
| 資訊   | `$info`    | 報告資訊性訊息。用於除錯與記錄模擬事件。      |
# 併發斷言 Concurrent Assertions
* 併發斷言檢查跨越多個時鐘週期的事件序列。
* SystemVerilog Assertions（SVA）中最強大也最常用的一種斷言形式，**主要用來描述和驗證設計的時序行為**。
* 與 Immediate Assertions 不同，Concurrent Assertions **不是在一個瞬間求值**，而是**描述跨時鐘週期發生的序列（sequence）或屬性（property）**，例如「如果某個信號發生，接下來幾個週期內應該看到另一個信號」。
* 併發斷言僅在有時鐘周期的情況下出現
* 測試表達式是基於所涉及變數的採樣值在時鐘邊緣進行計算的
* 它可以放在過程塊、模組、介面或程式定義中
* 區別併發斷言和立即斷言的關鍵字是property
## 基本結構
```
property <property_name>;
  @(clocking_event) <sequence_expression>;
endproperty
assert property (<property_name>);
```
| 組件                | 說明                              |
| ----------------- | ------------------------------- |
| `property`        | 定義時序屬性，可重複使用                    |
| `@()`             | 指定檢查的時鐘邊緣（通常是 `@(posedge clk)`） |
| `sequence`        | 定義事件的發生順序與時間間隔                  |
| `assert property` | 觸發並行斷言，進行驗證                     |
## 三種關鍵用途
| 關鍵字               | 用途                   |
| ----------------- | -------------------- |
| `assert property` | 驗證 property 是否成立     |
| `assume property` | 假設 property 在形式驗證中成立 |
| `cover property`  | 檢查是否曾經滿足過 property   |
## 常用時序操作符（Temporal Operators）
| 操作符           | 說明              |                          |
| ------------- | --------------- | ------------------------ |
| `##n`         | 延遲 n 個時鐘週期      |                          |
| \`            | ->\`            | 非重疊 implies（前項發生後，後項才開始） |
| \`            | =>\`            | 重疊 implies（前項和後項可同時開始）   |
| `[*n]`        | 重複 n 次          |                          |
| `[->n]`       | 在 n 個時鐘週期內發生一次  |                          |
| `throughout`  | 表示整個區間內某條件一直成立  |                          |
| `within`      | 某序列發生在另一序列時間範圍內 |                          |
| `first_match` | 比對序列中第一個符合條件的事件 |                          |
## 範例
1. 簡單握手協定
```
property handshake;
  @(posedge clk)
  req |-> ##1 ack;
endproperty

assert property(handshake);
```
* 在 posedge clk 發現 req 為真後，下一個時鐘週期（##1） ack 必須為真。
2. FIFO 滿時禁止寫入
```
property no_write_when_full;
  @(posedge clk)
  fifo_full |-> ##1 !write;
endproperty

assert property(no_write_when_full);
```
* 若 fifo_full 為真，下一個 cycle write 必須為假。
## Immediate Assertions vs Concurrent Assertions
| 比較項目                 | Immediate Assertions（即時斷言）      | Concurrent Assertions（並行斷言）                          |
| -------------------- | ------------------------------- | ---------------------------------------------------- |
| 📌 **語法位置**          | 嵌入在程序區塊中（如 `initial`, `always`） | 定義為 `property` 或 `sequence` 並用 `assert property` 等調用 |
| 🕒 **執行時機**          | **立即求值**（模擬時瞬間執行）               | **延遲求值**（根據時序、在多個 clock cycle 之間進行）                  |
| ⏱ **時序能力**           | 無法描述跨時間點行為，只能驗證某一時刻的條件          | 可描述事件之間的時序關係（如延遲、重複、持續等）                             |
| 🧠 **適合用途**          | 驗證簡單條件、參數範圍、即時錯誤檢查              | 協定驗證、流程驗證、複雜時序條件                                     |
| 💬 **語法簡單度**         | 簡單，直覺（類似 C 語言條件判斷）              | 較複雜，需要熟悉序列（sequence）與屬性（property）語法                  |
| 🔁 **可重複使用**         | 不易模組化或重複使用                      | 支援定義 `sequence` 和 `property`，便於封裝與重用                 |
| 🔄 **覆蓋分析**          | 可用 `$coverage`, `cover` 收集資訊    | 使用 `cover property` 精確收集時序行為覆蓋                       |
| ❌ **reset 忽略**       | 需額外用 `if (~reset)` 包住           | 可使用 `disable iff` 忽略 reset 期間的錯誤報告                   |
| 🧪 **與 Formal 工具搭配** | 支援，但功能有限                        | 完整支援，可直接套用於形式驗證環境                                    |
## 使用時機
| 使用場景                     | 建議斷言類型               |
| ------------------------ | -------------------- |
| 檢查變數是否符合某個邏輯或範圍          | Immediate            |
| 驗證在 reset 後 flag 一定為 0   | Immediate            |
| 驗證「某信號成立後，幾個 clock 內需反應」 | Concurrent           |
| 驗證 FIFO 不可滿時寫入、協定握手      | Concurrent           |
| formal tool 建模與輸入約束      | Concurrent（用 assume） |
## Sequence vs Property
| 名稱             | 說明                                         |
| -------------- | ------------------------------------------ |
| **`sequence`** | 描述一串事件「**如何**」在時間上發生（即時序行為）                |
| **`property`** | 用來定義某個「**時序條件**」是否該成立，可使用一個或多個 sequence 組成 |
# Sequence
* 定義事件之間的 時序規則（例如：信號在幾個 cycle 後發生、是否連續發生等）
* 常用在握手、延遲、持續等時序驗證情境
* 可重複使用，也可嵌套其他 sequence
## 語法
```
sequence <sequence_name>;
  @(posedge clk) expression1 ##delay expression2 ...;
endsequence
```
```
sequence handshake_seq;
  @(posedge clk)
  req ##1 ack;
endsequence
```
req 為真後，下一個週期（##1） ack 必須為真。
# Property
* 用來描述「如果發生 A，就要看到 B」這類因果條件
* 可以套用 sequence 或邏輯條件來形成完整的驗證目標
* 與 assert property / assume property / cover property 搭配使用
## 語法
```
property <property_name>;
  @(posedge clk)
  antecedent |-> consequent;
endproperty
```
* |-> 表示非重疊 implies（「如果」前面為真，則「之後」後面要為真）
```
sequence handshake_seq;
  @(posedge clk) req ##1 ack;
endsequence

property handshake_prop;
  @(posedge clk) handshake_seq;
endproperty

assert property (handshake_prop);
```
property 是使用 sequence 的容器，實際驗證條件是 req -> ack 的時序。
| 比較項目     | `sequence`                     | `property`                          |
| -------- | ------------------------------ | ----------------------------------- |
| 功能       | 定義一連串事件的時序關係                   | 定義時序條件（可以包含 `sequence`）             |
| 是否能直接斷言  | ❌ 不行，需放在 property 中使用          | ✅ 可以直接用 `assert property()`         |
| 結構層次     | 通常較低層（建構用）                     | 較高層（驗證用）                            |
| 可否組合其他語法 | ✅ 可以用 `and`, `or`, `##`, `[*]` | ✅ 可結合 `sequence`, `disable iff` 等語法 |
| 用途       | 建模時序行為                         | 驗證是否滿足特定時序行為                        |

## MISC
![image](https://github.com/user-attachments/assets/cec0bea4-7997-49e2-bd62-8fd1acf4c1fe)  
```
always_comb
begin
  a_ia: assert (a && b);
end
```
* 只有 a 或 b 發生變化時去 assertion 做檢查
![image](https://github.com/user-attachments/assets/89a300b5-9ef0-40c0-b323-c4c5401f115b)  
```
a_cc: assert property(@(posedge clk)
                                    not (a && b));
```
![image](https://github.com/user-attachments/assets/399a1456-b3b4-413d-80cc-966f780758ca)  
```
sequence s2;
  @(poseedge clk) $rose(a);  // 上一拍為低, 這拍為高
endsequence
```
![image](https://github.com/user-attachments/assets/098136e4-35ef-4686-80d0-3e1a4fc909fe)  
為甚麼不是 timestamp 1 的時候呢?  
因為 a 是因為 posedge 才驅動的, 所以一定會 posedge 之後 a 才拉起來, 所以在 timestamp 1 時 a 為 0  
```
sequence s3;
  @(poseedge clk) a || b;
endsequence
```
![image](https://github.com/user-attachments/assets/84a2b63c-6cb2-4f6f-b9d6-cf80065e5c04)  
這裡要看時鐘 posedge 左邊的值才採樣的值  
```
sequence s4;
  @(poseedge clk) a ##2 b;  // 當前採樣的 a 為高, 兩拍後 b 也採樣為高
endsequence
```
![image](https://github.com/user-attachments/assets/4b05dac5-66cc-45ee-b04c-cc4fda103690)  
```
sequence s6;
  @(poseedge clk) a ##2 b;  // 當前採樣的 a 為高, 兩拍後 b 也採樣為高
endsequence

property p6;
  not s6;
endproperty

a6: assert property(p6);
```
![image](https://github.com/user-attachments/assets/9931da76-b2c0-48d1-aa57-e4db8dcc0828)  
![image](https://github.com/user-attachments/assets/d2f65df9-2ad8-437f-ae2b-26df06cb3cd8)  
## Implication
```
property p8;
  @(poseedge clk) a |-> b;  // 在先行條件滿足時 (a), 在同一拍看後續表達式是否也滿足 (b)
endproperty

a8: assert property(p8);
```
![image](https://github.com/user-attachments/assets/9ceb345b-990d-461b-aef6-8f0c8772d7af)  
```
property p9;
  @(poseedge clk) a |=> b;  // 在先行條件滿足時 (a), 在下一拍看後續表達式是否也滿足 (b)
endproperty

a9: assert property(p9);
```
![image](https://github.com/user-attachments/assets/e03d2e75-ec96-45ec-b198-aa51bb25f3f7)  
```
property p12;
  @(poseedge clk) (a && b) |-> ##[1:3] c;  // 在任何一拍看 a 和 b 是否同時為高, 接下來 1 到 3 拍之間, c 應該至少在一個時間周期內為高
endproperty

a12: assert property(p12);
```
![image](https://github.com/user-attachments/assets/783817b2-8a29-4540-9245-3b13d0288680)  
```
property p13;
  @(poseedge clk) a |-> ##[1:$] b #[0:$] c;  // 無限時序 (不建議使用)
endproperty

a13: assert property(p13);
```
![image](https://github.com/user-attachments/assets/cd61df9e-0f3e-485b-92ef-36c6177fd117)  
```
sequence s15a;
  @(poseedge clk) a ##1 b;
endsequence

sequence s15b;
  @(poseedge clk) c ##1 d;
endsequence

property p15a;
  s15a |=> s15b;
endproperty

property p15b;
  s15a.ended |-> ##2 s15b.ended;  // 前一個 sequence 結束的點當作連接點, s15a 結束的點, 就是延遲的第一拍
endproperty

// s15a 和 s15b 是同樣的意思

a15a: assert property(p15a);
a15b: assert property(p15b);
```
```
property p17;
  @(poseedge clk) c ? d == a : d == b;
endproperty

a17: assert property(p17);
```
![image](https://github.com/user-attachments/assets/4968979c-4931-48f0-a14b-f32afa971da5)  
# $past
![image](https://github.com/user-attachments/assets/24153a20-0169-4cbd-a70a-b63c055e82d8)  
![image](https://github.com/user-attachments/assets/61c8927f-57b7-4cc2-a164-a1973357c8b1)  

# 連續重複運算
![image](https://github.com/user-attachments/assets/f421d00e-317a-4842-9e86-8d25e8766aab)  
![image](https://github.com/user-attachments/assets/77386488-61fe-4874-974e-13f7da8adf0e)  
![image](https://github.com/user-attachments/assets/9e2df2ed-ec59-4b62-b717-226f7a788a40)  
![image](https://github.com/user-attachments/assets/c5822bbf-42d3-432e-bb55-58285678cb32)  
![image](https://github.com/user-attachments/assets/214202ee-ccb7-4d58-be4c-17c796dd28f0)  

# 非連續跟隨重複
![image](https://github.com/user-attachments/assets/b5b7898f-cdc8-48a8-a25d-6f97f0ac0a6b)  
![image](https://github.com/user-attachments/assets/2b31cda3-b233-4a4b-8e8e-8d0dd18cdec7)  
a 三次拉起後, 緊接著 ##1
# 非連續非跟隨重複
![image](https://github.com/user-attachments/assets/7072c071-3c3c-49e9-b8fc-dd0b30aefea3)  
![image](https://github.com/user-attachments/assets/dd1779e5-8266-4b67-a6b0-fdcef5a8377d)  
a 拉高三次後有多隔一拍, 才 ##1

# And
![image](https://github.com/user-attachments/assets/001d9ed2-9f96-45cf-ba2c-bc93e52994ce)  
![image](https://github.com/user-attachments/assets/a5139046-4143-4441-8f78-3d601337fcc9)  

# Intersect
![image](https://github.com/user-attachments/assets/f388f57d-9028-4c29-ad07-eed589916f01)
![image](https://github.com/user-attachments/assets/efef1abb-00aa-4133-9f03-81a58bdec27d)  
![image](https://github.com/user-attachments/assets/6f34291a-2d4a-44b5-8723-68f92836ae77)  

# Or
![image](https://github.com/user-attachments/assets/6e1a8594-6345-4a4e-a9ff-7876815cdfbe)  
![image](https://github.com/user-attachments/assets/138391c3-8823-4c7d-9bbf-2a76acc390c4)  

# first_match
![image](https://github.com/user-attachments/assets/4b6fc907-a67b-49d4-831c-8a4d9563f5a0)  
![image](https://github.com/user-attachments/assets/0097e673-bf67-4043-9272-0ac321bd8c9e)  

# throughout
某條件或是某信號要一直為高
![image](https://github.com/user-attachments/assets/1203b0c5-bfca-4926-bddf-bf34e9001b2a)  
![image](https://github.com/user-attachments/assets/e746db31-3153-40c2-9a46-7bacfe772ce8)  
![image](https://github.com/user-attachments/assets/e01b1ce7-64fe-4ff1-9988-8ac96a3052a2)  

# Within
![image](https://github.com/user-attachments/assets/9ad18c59-6975-4c1d-87ae-e96d9174944c)  
![image](https://github.com/user-attachments/assets/79542841-0c5b-47cd-94ab-e112da6720c2)  

# disable iff
![image](https://github.com/user-attachments/assets/b6b62fbd-8acd-4bc4-b8bb-2361623ea5d8)  
可以在某些條件滿足的情況下, 禁止屬性檢查

# if..else
![image](https://github.com/user-attachments/assets/59d5aaef-f446-4f67-88a9-a18721b31af5)
PS: 只能用在後續算子中

# expect
cpu ready 拉高後
![image](https://github.com/user-attachments/assets/9ea2acb8-50f6-4bac-b471-eb6694c87d49)

# SVA local variable
![image](https://github.com/user-attachments/assets/849c1f97-c588-431c-9f10-f485e0fb051f)  
![image](https://github.com/user-attachments/assets/dbaa75ff-52bc-445c-8518-04561e780fde)  
PS: 放到 sequence 最後去暫存 (逗號之後)

# SVA 子程序
![image](https://github.com/user-attachments/assets/db33d30e-bd66-47cc-842d-7633441394fe)  

