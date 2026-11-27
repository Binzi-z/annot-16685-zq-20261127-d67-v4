# -*- coding: utf-8 -*-
"""sensitive_memory_return.py 的快速自检（秒级，供 CI 与人工复核）。

完整的 8 MiB / 十万步验证请直接运行：
    python sensitive_memory_return.py
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import sensitive_memory_return as smr


class BarrierDramaTests(unittest.TestCase):
    def test_all_invariants_hold(self):
        d = smr.barrier_drama()
        failed = [name for name, ok, _ in d["checks"] if not ok]
        self.assertEqual(failed, [])
        # 同号重发但引用代推进：旧凭据不可能恢复写
        self.assertEqual(d["hB"].hid, d["hB2"].hid)
        self.assertGreater(d["hB2"].gen, d["gen_B_old"])
        self.assertEqual(d["hA"].hid, d["hA2"].hid)
        self.assertGreater(d["hA2"].gen, d["hA"].gen)
        # 物理终态零泄漏
        self.assertEqual(d["pool"].physical_security_scan(), 0)

    def test_old_handle_replay_denied_by_generation(self):
        d = smr.barrier_drama()
        pool = d["pool"]
        # 旧凭据代落后于册中当代，裸 hid（代=0）重投同样被拒
        self.assertEqual(pool.write(d["hA"], 1), ("denied:stale",))
        self.assertEqual(pool.read(d["hB"]), ("denied:stale",))
        self.assertEqual(pool.write(d["hB"].hid, 1)[0], "denied:stale")


class ExhaustiveSmallPoolTests(unittest.TestCase):
    def test_depth_three_interleavings(self):
        r = smr.exhaustive_small_pool(depth=3)
        self.assertEqual(r["sequences"], len(smr.ALPHABET) ** 3)
        self.assertEqual(r["verdict_diffs"], 0)
        self.assertEqual(r["shadow_errors"], 0)
        # 四类关键拒绝在穷举中都必须真实出现
        for key in ("denied:busy", "denied:stale", "denied:write_revoked",
                    "denied:unsanitized", "denied:not_sharedable",
                    "denied:no_handle"):
            self.assertIn(key, r["denials"])


class WorkloadTests(unittest.TestCase):
    def test_deterministic_and_wellformed(self):
        a = smr.generate_workload(steps=2000, seed=7)
        b = smr.generate_workload(steps=2000, seed=7)
        self.assertEqual(a, b)
        kinds = {op[0] for op in a}
        self.assertTrue({"R", "H", "B", "S", "P"} <= kinds)

    def test_dual_implementations_agree_end_to_end(self):
        ops = smr.generate_workload(steps=1000, seed=11)
        p_sel = smr.SensitivePool(1 << 20)
        p_ref = smr.FullRefPool(1 << 20)
        b_sel, b_ref = smr.TokenBook(), smr.TokenBook()
        for op in ops:
            v1 = smr.drive_op(p_sel, b_sel, op)
            v2 = smr.drive_op(p_ref, b_ref, op)
            if op[0] in ("R", "H"):
                b_sel.remember_rent(op[1], v1)
                b_ref.remember_rent(op[1], v2)
            elif op[0] == "B":
                b_sel.remember_return(op[1])
                b_ref.remember_return(op[1])
            elif op[0] == "K":
                b_sel.remember_revoke(op[1], v1)
                b_ref.remember_revoke(op[1], v2)
            self.assertEqual(smr.comparable(v1), smr.comparable(v2))
            self.assertEqual(p_sel.holders, p_ref.holders)
            self.assertEqual(p_sel.busy, p_ref.busy)
            self.assertEqual(p_sel.dirty, p_ref.dirty)
        for pool, book in ((p_sel, b_sel), (p_ref, b_ref)):
            for serial, h in list(book.live.items()):
                pool.return_handle(h)
                book.remember_return(serial)
            pool.sanitize()
            pool.reconcile_shadow(full=True)
            self.assertEqual(pool.physical_security_scan(), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
