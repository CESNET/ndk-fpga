#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Package for plotting statistics from logger_stats


import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm
import seaborn as sns


def load_data(file_name : str):
    """
    Load `*.npz` file created by logger_stats

    Parameters
    ----------
       file_name (str): *.npz file with statistics
    """

    return np.load(file_name, allow_pickle=True)['arr_0'].item()


def plot_counter(data, x, y, title, log=False, diff=True):
    """
    Plot historical values of data_logger's counter

    Parameters
    ----------
        data : dict
            Data in shape `{'Stat A': list, ...}`
        x : str
            X axis label
        y : str
            Y axis label
        log : bool
            Make Y axis logarithmic
        diff : bool
            Plot only differences between historical measurements (data_logger increment counters)

    Example:

        ```
        from graph_tools.graph_tools import *

        stats = load_data('stats.npz')

        node = pd.DataFrame.from_dict(stats['Stats A']['Counters'])
        selected = ['Counter A', 'Counter B']

        # Plot single counter
        plot_counter(node['Counter X'], 'Time', 'Requests', 'Plot title')

        # Plot multiple counters
        plot_counter(node[selected], 'Time', 'Requests', 'Plot title')
        ```
    """

    data = pd.DataFrame(data)

    if diff:
        data = data.diff()

    plt.figure(figsize=(20, 6))
    sns.lineplot(data=data)
    plt.title(title)
    plt.xlabel(x)
    plt.ylabel(y)
    if log:
        plt.yscale('log')


def plot_value(data, x : str, y : str, title : str, zoom : bool = True, log : bool = False):
    """
    Plot histogram of data_logger's value interface

    Parameters
    ----------
        data : dict
            Data in shape `{'hist_x': list, 'hist': 2D array}`
        x : str
            X axis label
        y : str
            Y axis label
        log : bool
            Make Y axis logarithmic
        zoom : bool
            Zoom only to non zero area of the histogram
    """

    data = pd.DataFrame({'x': data['hist_x'], 'y': np.array(data['hist']).sum(axis=0)})

    plt.figure(figsize=(20, 6))
    sns.lineplot(data=data, x='x', y='y')
    plt.title(title)
    plt.xlabel(x)
    plt.ylabel(y)
    if log:
        plt.yscale('log')

    plt.fill_between(data['x'], data['y'], alpha=0.3, color="skyblue")

    if zoom:
        non_zero_indices = np.where(np.array(data['y']) > 0)[0]
        if len(non_zero_indices) > 1:
            plt.xlim(data['x'][non_zero_indices[0]], data['x'][non_zero_indices[-1]])


def downsize(data, x, y, ticks):
    orig_x, orig_y = data.shape

    if orig_x <= x or orig_y <= y:
        return data, ticks

    tile_x = orig_x // x
    tile_y = orig_y // y

    print(x, y, tile_x, tile_y)

    tiles = data.reshape(-1, tile_x, y, tile_y)
    tiles = tiles.transpose(0, 2, 1, 3)
    tiles = tiles.sum(axis=3).sum(axis=2)

    #pad = tile_x - orig_x % x
    #print(pad, tile_x, orig_x, x)
    #ticks = np.pad(ticks, (0, pad), mode='constant', constant_values=0)
    ticks = ticks.reshape(-1, y).mean(axis=1)

    return (tiles, ticks)


def trim_zeros(data, ticks):
    # First non zero row
    first_index = np.any(data != 0, axis=1).argmax()
    last_index = data.shape[0] - np.any(data != 0, axis=1)[::-1].argmax() - 1

    if first_index + 2 > last_index:
        first_index = max(0, first_index - 2)
        last_index = min(data.shape[0], last_index + 2)

    return (data[first_index : last_index + 1], ticks[first_index : last_index + 1])


def downsize_ratio(data, max_x, max_y):
    x, y = data.shape

    while x > max_x:
        if x / 2 != x // 2:
            break
        else:
            x //= 2

    while y > max_y:
        if y / 2 != y // 2:
            break
        else:
            y //= 2

    return (x, y)


def plot_value_2d(
        data,
        x : str,
        y : str,
        title : str,
        zoom : bool = True,
        log : bool = False,
        downsize_size=None,
        ticks=None
):
    """
    Plot 2D histogram of data_logger's value interface history

    Parameters
    ----------
        data : dict
            Data in shape `{'hist_x': list, 'hist': 2D array}`
        x : str
            X axis label
        y : str
            Y axis label
        log : bool
            Make Y axis logarithmic
        zoom : bool
            Zoom only to non zero area of the histogram
        ticks : [float]
            Custom values for x axis
    """

    x_ticks = list(map(lambda x: round(x), data['hist_x']))
    hist = np.array(data['hist']).transpose(1, 0)

    if (hist == 0).all():
        print(f"Plot {title} contains all zeros")
        return

    if zoom:
        hist, x_ticks = trim_zeros(hist, x_ticks)

    if downsize_size is not None:
        x_size, y_size = downsize_ratio(hist, *downsize_size)
        hist, x_ticks = downsize(hist, x_size, y_size, np.array(x_ticks))

    if len(x_ticks) <= 1:
        print(f"More logs are needed ({hist})")
        return

    if ticks is None:
        ticks = [f'{i}' for i in range(0, hist.shape[1])]

    data = pd.DataFrame(
        hist,
        index=[x_ticks[i] for i in range(0, hist.shape[0])],
        columns=ticks
    )

    def min_max_normalize(df):
        return (df - df.min()) / (df.max() - df.min())
    data = data.apply(min_max_normalize)

    norm = None if not log else LogNorm()
    plt.figure(figsize=(20, 8))
    sns.heatmap(data=data, norm=norm, cmap='jet')
    plt.title(title)
    plt.xlabel(x)
    plt.ylabel(y)

    # Reduce number of ticks
    for ind, label in enumerate(plt.gca().get_yticklabels()):
        label.set_visible(ind % 5 == 0)


def plot_value_both(*args, **kwargs):
    plot_value(*args, **kwargs)
    plot_value_2d(*args, **kwargs)


def only_numeric(data):
    df = pd.DataFrame(data)
    mask = df.apply(lambda row: row.apply(lambda x: pd.api.types.is_numeric_dtype(type(x))).all(), axis=1)
    df = df[mask]
    return df


def legend(labels, loc='upper left', **kwargs):
    plt.legend(labels, bbox_to_anchor=(1, 1), loc=loc, **kwargs)
