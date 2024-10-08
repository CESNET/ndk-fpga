#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm


class GraphGen:
    def __init__(self, folder="", ratio=(10, 4), output=[".pdf", ".png"]):
        self.folder = folder
        self.ratio = ratio
        self.output = output

        # Clear fig folder
        if not os.path.exists(self.folder):
            os.mkdir(self.folder)
        else:
            for file in os.listdir(self.folder):
                for e in self.output:
                    if file.endswith(e):
                        os.remove(self.folder + file)

    def init_plots(self, rows=1, cols=1, title=None, **kwargs):
        self.fig, self.ax = plt.subplots(rows, cols, figsize=self.ratio, **kwargs)
        if title:
            plt.suptitle(title, y=0.95)
        self.fig.subplots_adjust(hspace=0.05)

    def set_xlabel(self, label, index=None):
        ax = self.indexToAx(index)
        ax.set_xlabel(label)

    def set_ylabel(self, label, index=None):
        ax = self.indexToAx(index)
        ax.set_ylabel(label)

    def plot_save(self, file_name):
        for i in self.output:
            plt.savefig(self.folder + file_name + i)
        plt.close()

    def basic_plot(self, x, y, style='o-', index=None, colors=None, width=1):
        ax = self.indexToAx(index)

        for i in range(0, len(y)):
            if colors is not None:
                ax.plot(x, y[i], style, color=colors[i], linewidth=width)
            else:
                ax.plot(x, y[i], style, linewidth=width)

    def histogram_plot(self, x, y, index=None, colors=None, log=False):
        ax = self.indexToAx(index)

        for i in range(0, len(y)):
            if colors is not None:
                ax.hist(y[i], bins=x, log=log, color=colors[i])
            else:
                ax.hist(y[i], bins=x, log=log)

    def stack_plot(self, x, y, index=None, colors=None, labels=(), log=False, **kwargs):
        y = np.vstack(y)
        ax = self.indexToAx(index)

        if log:
            ax.yscale('log')
        ax.stackplot(x, y, colors=colors, labels=labels, **kwargs)

    def plot_2d(self, data, index=None, log=False, limits=None, min=None, ip="none", cmap='jet', **kwargs):
        ax = self.indexToAx(index)
        log = LogNorm() if log else None  # "log" if log else None
        if min is not None:
            data[data <= min] = np.nan

        im = ax.imshow(
            data,
            extent=limits,
            aspect='auto',
            norm=log,
            cmap=cmap,
            origin='lower',
            interpolation=ip,
            **kwargs)

        cax = ax.inset_axes([1.01, 0.05, 0.02, 0.9])
        self.fig.colorbar(im, cax=cax)

    def legend(self, labels, index=None, loc='upper left', **kwargs):
        #plt.legend(bbox_to_anchor=(1, 0), loc=loc, **kwargs)
        #plt.legend(loc=loc, **kwargs)
        ax = self.indexToAx(index)
        #ax.legend(labels)
        ax.legend(labels, bbox_to_anchor=(1, 1), loc=loc, **kwargs)

    def plt(self):
        return plt

    def axis(self, index=None):
        return self.indexToAx(index)

    def indexToAx(self, index):
        ax = self.ax
        if index is not None:
            ax = ax[index]
        return ax
