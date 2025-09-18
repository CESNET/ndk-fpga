
from ..utils import SerializableHeader


class RQHeader(SerializableHeader):
    items = list(zip(
        [
            'at', 'addr', 'dword_count', 'req_type', 'poisoned_request',
            'req_id', 'tag', 'completer_id', 'req_id_en', 'tc', 'attr', 'force_ecrc',
        ],
        [2, 62, 11, 4, 1, 16, 8, 16, 1, 3, 3, 1],
    ))


class CQHeader(SerializableHeader):
    items = list(zip(
        [
            'at', 'addr', 'dword_count', 'req_type', 'res1',
            'req_id', 'tag', 'tgt_func', 'bar_id', 'bar_apper', 'tc', 'attr', 'res2',
        ],
        [2, 62, 11, 4, 1, 16, 8, 8, 3, 6, 3, 3, 1],
    ))


class RCHeader(SerializableHeader):
    items = list(zip(
        [
            'addr', 'error_code', 'byte_count', 'locked_read_completion',
            'request_completed', 'res1', 'dword_count', 'completion_status',
            'poisoned_completion', 'res2', 'requester_id', 'tag', 'completer_id',
            'res3', 'tc', 'attr', 'res4',
        ],
        [12, 4, 13, 1, 1, 1, 11, 3, 1, 1, 16, 8, 16, 1, 3, 3, 1],
    ))


class CCHeader(SerializableHeader):
    items = list(zip(
        [
            'lower_address', 'r1', 'at', 'r2', 'byte_count', 'lrc', 'r3',
            'dword_count', 'completion_status', 'poisoned', 'r4', 'rid',
            'tag', 'cid', 'cid_en', 'tc', 'attr', 'ecrc'
        ],
        [7, 1, 2, 6, 13, 1, 2, 11, 3, 1, 1, 16, 8, 16, 1, 3, 3, 1],
    ))


class RQUser(SerializableHeader):
    items = list(zip(
        [
            'first_be0', 'first_be1', 'last_be0', 'last_be1', 'addr_offset0',
            'addr_offset1', 'sop', 'sop0', 'sop1', 'eop', 'eop0', 'eop1',
            'discontinue', 'tph_present', 'tph_type', 'tph_st_tag',
            'tph_indirect_tag_en', 'seq_num0', 'seq_num1', 'parity',
        ],
        [4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 4, 4, 1, 2, 4, 16, 2, 6, 6, 64],
    ))


class CQUser(SerializableHeader):
    items = list(zip(
        [
            'firstBe0', 'firstBe1', 'lastBe0', 'lastBe1', 'byte_en', 'sop0', 'sop1',
            'sop_ptr0', 'sop_ptr1', 'eop0', 'eop1', 'eop_ptr0', 'eop_ptr1', 'discontiune',
            'tph_present', 'tph_type', 'tph_sh_tag', 'parity'
        ],
        [4, 4, 4, 4, 64, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4, 8, 64],
    ))


class RCUser(SerializableHeader):
    items = list(zip(
        [
            'be', 'sop', 'sop0', 'sop1', 'sop2', 'sop3',
            'eop', 'eop0', 'eop1', 'eop2', 'eop3', 'discontinue', 'parity'
        ],
        [64, 4, 2, 2, 2, 2, 4, 4, 4, 4, 4, 1, 64],
    ))
