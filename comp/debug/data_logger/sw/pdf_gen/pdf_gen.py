#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>


class PDFGen:
    def __init__(self):
        self.res = ""

    def heading(self, lvl, txt):
        self.res += ('#' * lvl) + ' ' + txt + "\n\n"

    def text(self, txt):
        self.res += txt + "\n\n"

    def table(self, header, rows):
        self.res += '|'
        for i in header:
            self.res += i + '|'
        self.res += '\n'

        self.res += '|' + ('--|' * len(header)) + '\n'
        for i in rows:
            self.res += '|'
            for j in i:
                self.res += str(j) + '|'
            self.res += '\n'

        self.res += '\n'

    def image(self, path):
        self.res += f"![]({path})\n\n"

    def save(self, file):
        with open(file + '.md', 'w') as f:
            f.write(self.res)
