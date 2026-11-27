# 共享敏感缓冲归还后的隔离验证

题面见 `task/PROMPT.txt`。仓库附本地合成输入 `fixture.json` 及其格式检查。

## 交付物

- `sensitive_memory_return.py` —— 单文件、仅 Python 3.12 标准库的可验证模型
  （`array` / `bytearray` / `threading.Barrier` / `itertools` / `random` / `csv`）。
- `tests/test_sensitive_memory_return.py` —— 秒级自检（屏障剧、深度 3 穷举、
  确定性负载、双实现端到端对账），与原 `tests/test_fixture.py` 并存。

## 四条独立证据

| 证据 | 建模 | 留痕位置 |
| --- | --- | --- |
| 引用代 | 全局代单调推进；句柄是带代的能力凭据，逐字节记录所属代与历史水位 `hwm` | `gen[]`、`Handle.gen`、`hwm` |
| 共享区间 | 逐字节 holder 引用计数 + busy 位图，计数 > 0 不得移交 | `holders[]`、`busy[]` |
| 已失效写权 | 凭据 `writable` 位撤销后读仍合法、写永远拒绝；共享者写权独立 | `verdict_write` → `denied:write_revoked` |
| 实际擦除字节 | 物理 `bytearray` 真正清零并逐段记录；逻辑空闲 ≠ 物理擦除，未擦除空闲字节拒绝再租 | `mem[]`、`EraseEvent` 日志、`denied:unsanitized` |

每个池内置一张**独立影子表** `Shadow`：它不读取池的任何数组，靠同一操作流
自行复演全部判定与逐字节状态，每次策略判定先与池侧结论对账，提交后再做
增量/全量逐字节比对；任何分歧立即抛 `ShadowMismatch`。

## 程序三段验证

1. **双线程 Barrier 剧（8 道屏障）**：租户 A 撤销写权后仍持旧读引用；租户 B
   先归还相交切片并竞争复用——先被 `denied:busy` 挡下（A 仍持有），A 归还后
   又被 `denied:unsanitized` 挡下（实物内存仍残留旧租户字节）；擦除后同地址
   重租拿到**同号但新代**的句柄，A/B 的旧凭据同号重投一律 `denied:stale`。
2. **小池穷举**：8 字节池上枚举 15 种操作的全部深度 4 线性化（50,625 条），
   精确擦除实现与全量块擦除参考实现逐条判定比对、各自与影子表全量对账。
3. **8 MiB / 十万步合成借还**（32 租户、确定性种子 20261128）：报告存活租约
   区间并集峰值、延迟归还区峰值、每次真正擦除范围（同时写
   `erase_selective.csv` / `erase_full_reference.csv`）、引用代水位、拒绝
   分布，以及与全量参考实现的差异。

## 运行

```powershell
python sensitive_memory_return.py          # 完整验证，约 1 分钟
python -m unittest discover -s tests -v     # 快速自检 + 原 fixture 检查
```

## 最近一次完整运行的关键结果

- 屏障剧 17 项断言全部 PASS；穷举 50,625 条序列判定分歧 0、影子对账错误 0。
- 十万步（92,163 条有效操作）两实现 verdict 完全一致，终态物理泄漏 0 字节。
- 精确擦除 24,245 段 / 4.20 MiB；全量块擦除参考 437,683 段 / 688.71 MiB
  （163.9× 过擦除），差异只在擦除工作量，不在安全性与判定流。
