using DeskFrame.Core;
using DeskFrame.Properties;
using DeskFrame.Shaders;
using DeskFrame.Util;
using IWshRuntimeLibrary;
using Microsoft.Win32;
using Microsoft.WindowsAPICodePack.Shell;
using System.Collections;
using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Controls.Primitives;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Interop;
using System.Windows.Markup;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Media.Imaging;
using System.Windows.Shapes;
using System.Windows.Shell;
using System.Windows.Threading;
using WindowsDesktop;
using Wpf.Ui.Controls;
using static DeskFrame.Util.Interop;
using Application = System.Windows.Application;
using Binding = System.Windows.Data.Binding;
using Brush = System.Windows.Media.Brush;
using Brushes = System.Windows.Media.Brushes;
using Color = System.Windows.Media.Color;
using ColorConverter = System.Windows.Media.ColorConverter;
using DataFormats = System.Windows.DataFormats;
using DataObject = System.Windows.DataObject;
using DragDropEffects = System.Windows.DragDropEffects;
using DragEventArgs = System.Windows.DragEventArgs;
using File = System.IO.File;
using ListView = Wpf.Ui.Controls.ListView;
using ListViewItem = System.Windows.Controls.ListViewItem;
using MenuItem = Wpf.Ui.Controls.MenuItem;
using MessageBox = Wpf.Ui.Controls.MessageBox;
using MessageBoxResult = Wpf.Ui.Controls.MessageBoxResult;
using MouseEventArgs = System.Windows.Input.MouseEventArgs;
using Path = System.IO.Path;
using Point = System.Drawing.Point;
using Rectangle = System.Drawing.Rectangle;
using TextBlock = Wpf.Ui.Controls.TextBlock;
using TextBox = System.Windows.Controls.TextBox;
namespace DeskFrame
{
    public partial class DeskFrameWindow : System.Windows.Window
    {
        private readonly List<Particle> particles = new List<Particle>();
        private readonly List<Ellipse> visuals = new List<Ellipse>();

        private GrayscaleEffect _grayscaleEffect;
        ShellContextMenu scm = new ShellContextMenu();
        public Instance Instance { get; set; }
        public string _currentFolderPath;
        private FileSystemWatcher _fileWatcher = new FileSystemWatcher();
        private FileSystemWatcher _parentWatcher = new FileSystemWatcher();
        public BulkObservableCollection<FileItem> FileItems { get; set; }

        private DispatcherTimer? _debounceTimer;

        // Static Thumbnail STA Worker Thread & Cache
        private static readonly System.Collections.Concurrent.ConcurrentDictionary<(string Path, int Size, DateTime LastWrite), BitmapSource?> _thumbnailCache =
            new System.Collections.Concurrent.ConcurrentDictionary<(string Path, int Size, DateTime LastWrite), BitmapSource?>();

        private static readonly System.Collections.Concurrent.BlockingCollection<ThumbnailRequest> _thumbnailQueue =
            new System.Collections.Concurrent.BlockingCollection<ThumbnailRequest>();

        private static readonly Thread _thumbnailWorkerThread;

        private class ThumbnailRequest
        {
            public string Path { get; set; } = string.Empty;
            public int Size { get; set; }
            public bool IsShortcut { get; set; }
            public bool ShowShortcutArrow { get; set; }
            public double WindowsScalingFactor { get; set; }
            public TaskCompletionSource<BitmapSource?> Tcs { get; set; } = new TaskCompletionSource<BitmapSource?>();
        }

        static DeskFrameWindow()
        {
            _thumbnailWorkerThread = new Thread(ProcessThumbnailQueue)
            {
                IsBackground = true,
                Name = "STA Thumbnail Worker"
            };
            _thumbnailWorkerThread.SetApartmentState(ApartmentState.STA);
            _thumbnailWorkerThread.Start();
        }

        private static void ProcessThumbnailQueue()
        {
            foreach (var request in _thumbnailQueue.GetConsumingEnumerable())
            {
                try
                {
                    BitmapSource? thumbnail = null;
                    if (request.IsShortcut)
                    {
                        thumbnail = GetThumbnailWithOverlay(request.Path, request.Size, request.ShowShortcutArrow, request.WindowsScalingFactor);
                    }
                    else
                    {
                        thumbnail = GetThumbnailInternal(request.Path, request.Size);
                    }
                    request.Tcs.SetResult(thumbnail);
                }
                catch (Exception ex)
                {
                    request.Tcs.SetException(ex);
                }
            }
        }

        public bool VirtualDesktopSupported;
        IntPtr hwnd;
        IntPtr shellView = IntPtr.Zero;

        private bool _dragdropIntoFolder;
        public int _itemPerRow;
        public int ItemPerRow
        {
            get => _itemPerRow;
            set
            {
                if (_itemPerRow != value)
                {
                    _itemPerRow = value;
                }
            }
        }
        bool _dragMovingWinddow = false;


        private List<FileItem> _selectedItems = new List<FileItem>();
        private FileItem _draggedItem;
        private FileItem _itemUnderCursor;
        private FileItem _itemCurrentlyRenaming;
        string _dropIntoFolderPath;
        FrameworkElement _lastBorder;
        private bool _isRenaming = true;
        private bool _isTopmost = false;
        private bool _isRenamingFromContextMenu = false;
        private bool _canChangeItemPosition = false;
        private bool _bringForwardForMove = false;
        private bool _isDragging = false;
        private FileItem? _pendingDragItem = null;
        private Border? _pendingDragBorder = null;
        private System.Windows.Point _dragStartPoint;
        private bool _mouseIsOver;
        private bool _contextMenuIsOpen = false;
        private bool _fixIsOnBottomInit = true;
        private bool _didFixIsOnBottom = false;
        private bool _isMinimized = false;
        private bool _isIngrid = true;
        private bool _grabbedOnLeft;
        private int _snapDistance = 8;
        private int _gridSnapDistance = 10;
        private int _currentVD;
        int _oriPosX, _oriPosY;
        private bool _isBlack = true;
        private bool _checkForChages = false;
        private bool _canAutoClose = true;
        private bool _isLocked = false;
        private bool _isOnTop = false;
        private bool _isOnBottom = false;
        private bool _isLeftButtonDown = false;
        bool _canAnimate = true;
        private double _originalHeight;
        public int neighborFrameCount = 0;
        public int _previousItemPerRow = 0;
        private double _previousHeight = -1;
        public bool isMouseDown = false;
        private ICollectionView _collectionView;
        private CancellationTokenSource _cts = new CancellationTokenSource();
        private CancellationTokenSource loadFilesCancellationToken = new CancellationTokenSource();
        private CancellationTokenSource _changeIconSizeCts = new CancellationTokenSource();
        private CancellationTokenSource _adjustPositionCts;
        public DeskFrameWindow WonRight = null;
        public DeskFrameWindow WonLeft = null;

        ContextMenu contextMenu = new ContextMenu();
        MenuItem nameMenuItem;
        MenuItem dateModifiedMenuItem;
        MenuItem dateCreatedMenuItem;
        MenuItem fileTypeMenuItem;
        MenuItem fileSizeMenuItem;
        MenuItem ascendingMenuItem;
        MenuItem descendingMenuItem;
        MenuItem CustomItemOrderMenuItem;
        MenuItem CustomItemOrderEnabledMenuItem;
        MenuItem folderOrderMenuItem;
        MenuItem folderFirstMenuItem;
        MenuItem folderLastMenuItem;
        MenuItem folderNoneMenuItem;

        private string _fileCount;
        private int _folderCount = 0;
        private DateTime _lastUpdated;
        private string _folderSize;
        private double _itemWidth;
        private double _windowsScalingFactor;

        public enum SortBy
        {
            NameAsc = 1,
            NameDesc = 2,
            DateModifiedAsc = 3,
            DateModifiedDesc = 4,
            DateCreatedAsc = 5,
            DateCreatedDesc = 6,
            FileTypeAsc = 7,
            FileTypeDesc = 8,
            ItemSizeAsc = 9,
            ItemSizeDesc = 10,
        }

        public static ObservableCollection<FileItem> SortFileItems(ObservableCollection<FileItem> fileItems, int sortBy, int folderOrder)
        {
            IEnumerable<FileItem> items = fileItems;

            var sortOptions = new Dictionary<int, Func<IEnumerable<FileItem>, IOrderedEnumerable<FileItem>>>
            {
                { (int)SortBy.NameAsc, x => x.OrderBy(i => Regex.Replace(i.Name ?? "", @"\d+", m => m.Value.PadLeft(10, '0')), StringComparer.OrdinalIgnoreCase)},
                { (int)SortBy.NameDesc,x => x .OrderByDescending(i => Regex.Replace(i.Name ?? "", @"\d+", m => m.Value.PadLeft(10, '0')), StringComparer.OrdinalIgnoreCase)},
                { (int)SortBy.DateModifiedAsc, x => x.OrderBy(i => i.DateModified) },
                { (int)SortBy.DateModifiedDesc, x => x.OrderByDescending(i => i.DateModified) },
                { (int)SortBy.DateCreatedAsc, x => x.OrderBy(i => i.DateCreated) },
                { (int)SortBy.DateCreatedDesc, x => x.OrderByDescending(i => i.DateCreated) },
                { (int)SortBy.FileTypeAsc, x => x.OrderBy(i => i.FileType) },
                { (int)SortBy.FileTypeDesc, x => x.OrderByDescending(i => i.FileType) },
                { (int)SortBy.ItemSizeAsc, x => x.OrderBy(i => i.ItemSize) },
                { (int)SortBy.ItemSizeDesc, x => x.OrderByDescending(i => i.ItemSize) },
            };

            if (sortOptions.TryGetValue(sortBy, out var sorter))
                items = sorter(items);

            if (folderOrder == 1)
                items = items.OrderBy(i => !i.IsFolder);
            else if (folderOrder == 2)
                items = items.OrderBy(i => i.IsFolder);

            return new ObservableCollection<FileItem>(items);
        }



        public async Task<List<FileSystemInfo>> SortFileItemsToList(List<FileSystemInfo> fileItems, int sortBy, int folderOrder)
        {
            var fileItemSizes = new List<(FileSystemInfo item, long size)>();

            foreach (var item in fileItems)
            {
                long size = await GetItemSizeAsync(item);
                fileItemSizes.Add((item, size));
            }

            var sortOptions = new Dictionary<int, Func<List<(FileSystemInfo item, long size)>, IOrderedEnumerable<(FileSystemInfo item, long size)>>>
                {
                    { (int)SortBy.NameAsc, x => x.OrderBy(i => Regex.Replace(i.item.Name ?? "", @"\d+", m => m.Value.PadLeft(10, '0')), StringComparer.OrdinalIgnoreCase)},
                    { (int)SortBy.NameDesc,x => x .OrderByDescending(i => Regex.Replace(i.item.Name ?? "", @"\d+", m => m.Value.PadLeft(10, '0')), StringComparer.OrdinalIgnoreCase)},
                    { (int)SortBy.DateModifiedAsc, x => x.OrderBy(i => i.item.LastWriteTime) },
                    { (int)SortBy.DateModifiedDesc, x => x.OrderByDescending(i => i.item.LastWriteTime) },
                    { (int)SortBy.DateCreatedAsc, x => x.OrderBy(i => i.item.CreationTime) },
                    { (int)SortBy.DateCreatedDesc, x => x.OrderByDescending(i => i.item.CreationTime) },
                    { (int)SortBy.FileTypeAsc, x => x.OrderBy(i => i.item.Extension) },
                    { (int)SortBy.FileTypeDesc, x => x.OrderByDescending(i => i.item.Extension) },
                    { (int)SortBy.ItemSizeAsc, x => x.OrderBy(i => i.size) },
                    { (int)SortBy.ItemSizeDesc, x => x.OrderByDescending(i => i.size) },
                };

            var sortedItems = sortOptions.TryGetValue(sortBy, out var sorter)
                ? sorter(fileItemSizes).ToList()
                : fileItemSizes.ToList();

            if (folderOrder == 1)
                sortedItems = sortedItems.OrderBy(i => i.item is FileInfo).ToList();
            else if (folderOrder == 2)
                sortedItems = sortedItems.OrderBy(i => i.item is DirectoryInfo).ToList();

            var sortedFileInfos = sortedItems.Select(x => x.item).ToList();

            return sortedFileInfos;
        }
        public void SortCustomOrder(List<FileSystemInfo> items, List<Tuple<string, string>> customOrderedItems)
        {
            if (items == null || items.Count == 0 || customOrderedItems == null || customOrderedItems.Count == 0)
            {
                return;
            }
            foreach (var t in customOrderedItems)
            {
                string fileId = t.Item1;
                if (!int.TryParse(t.Item2, out int targetIndex))
                {
                    continue;
                }
                var itemToMove = items.FirstOrDefault(f => GetFileId(f.FullName!).ToString() == fileId);

                if (itemToMove == null)
                {
                    continue;
                }

                int currentIndex = items.IndexOf(itemToMove);

                if (currentIndex == targetIndex)
                {
                    continue;
                }
                if (targetIndex < 0 || targetIndex >= items.Count)
                {
                    continue;
                }
                items.RemoveAt(currentIndex);
                items.Insert(targetIndex, itemToMove);
            }
        }


        public void SortCustomOrderOc(ObservableCollection<FileItem> items, List<Tuple<string, string>> customOrderedItems)
        {

            if (items == null || items.Count == 0 || customOrderedItems == null || customOrderedItems.Count == 0)
            {
                return;
            }
            foreach (var t in customOrderedItems)
            {
                string fileId = t.Item1;
                if (!int.TryParse(t.Item2, out int targetIndex)) continue;

                var itemToMove = items.FirstOrDefault(f => GetFileId(f.FullPath!).ToString() == fileId);
                if (itemToMove == null) continue;

                int currentIndex = items.IndexOf(itemToMove);
                if (currentIndex != targetIndex && targetIndex >= 0 && targetIndex < items.Count)
                {
                    items.Move(currentIndex, targetIndex);
                }
            }
        }

        public void FirstRowByLastAccessed(List<FileSystemInfo> items, List<string> lastAccessedFileIds, int topN)
        {
            if (items == null || items.Count == 0 || lastAccessedFileIds == null || lastAccessedFileIds.Count == 0 || topN <= 0)
                return;

            var fileLookup = items
                .Where(f => f.FullName != null)
                .GroupBy(f => GetFileId(f.FullName).ToString())
                .ToDictionary(g => g.Key, g => g.ToList());

            var topIds = lastAccessedFileIds
                .Where(id => fileLookup.ContainsKey(id))
                .Take(topN)
                .ToList();

            var topFiles = new List<FileSystemInfo>();
            foreach (var id in topIds)
            {
                if (!fileLookup.ContainsKey(id))
                    continue;
                topFiles.AddRange(fileLookup[id]);
            }

            var remainingFiles = items.Except(topFiles).ToList();
            items.Clear();
            items.AddRange(topFiles);
            items.AddRange(remainingFiles);
        }

        private async Task<long> GetItemSizeAsync(FileSystemInfo entry, CancellationToken token = default)
        {
            if (entry is FileInfo fileInfo)
            {
                return fileInfo.Length;
            }
            else if (entry is DirectoryInfo directoryInfo && Instance.CheckFolderSize)
            {
                return await Task.Run(() => GetDirectorySize(directoryInfo, token), token);
            }

            return 0;
        }
        private long GetDirectorySize(DirectoryInfo directory, CancellationToken token)
        {
            long size = 0;

            try
            {
                foreach (var file in directory.EnumerateFiles("*", SearchOption.TopDirectoryOnly))
                {
                    token.ThrowIfCancellationRequested();
                    size += file.Length;
                }

                Parallel.ForEach(directory.EnumerateDirectories("*", SearchOption.TopDirectoryOnly), (subDir) =>
                {
                    token.ThrowIfCancellationRequested();
                    Interlocked.Add(ref size, GetDirectorySize(subDir, token));
                });
            }
            catch
            {
            }

            return size;
        }
        private void MouseLeaveWindow(bool animateActiveColor = true)
        {
            var timer = new System.Windows.Forms.Timer();
            timer.Interval = 1;
            timer.Tick += (s, e) =>
            {
                if (animateActiveColor && !IsCursorWithinWindowBounds() && (GetAsyncKeyState(0x01) & 0x8000) == 0)
                {
                    _mouseIsOver = false;
                    AnimateActiveColor(Instance.AnimationSpeed);
                    if (Instance.HideTitleBarIconsWhenInactive)
                    {
                        TitleBarIconsFadeAnimation(false);
                    }
                    if (!_contextMenuIsOpen)
                    {
                        _selectedItems.Clear();
                        foreach (var fileItem in FileItems)
                        {
                            fileItem.IsSelected = false;
                            fileItem.Background = Brushes.Transparent;
                        }
                    }
                    if (!_isRenamingFromContextMenu)
                    {
                        _itemCurrentlyRenaming = null;
                    }
                }
                if (!IsCursorWithinWindowBounds() && (GetAsyncKeyState(0x01) & 0x8000) == 0) // Left mouse button is not down
                {

                    if (_canAutoClose)
                    {
                        FilterTextBox.Text = null;
                        //   FilterTextBox.Visibility = Visibility.Collapsed;
                    }
                    if (!_isTopmost)
                    {
                        this.SetNoActivate();
                    }
                    if (_didFixIsOnBottom) _fixIsOnBottomInit = false;

                    var timer = new DispatcherTimer
                    {
                        Interval = TimeSpan.FromMilliseconds(1)
                    };
                    timer.Tick += (s, args) =>
                    {
                        if (!_dragdropIntoFolder) ;
                        {
                            Dispatcher.InvokeAsync(() =>
                            {
                                FileListView.SelectedIndex = -1;
                                foreach (var item in FileListView.Items)
                                {
                                    var container = FileListView.ItemContainerGenerator.ContainerFromItem(item) as ListViewItem;
                                    if (container != null) container.IsSelected = false;
                                }
                            });
                            timer.Stop();
                        }
                    };
                    timer.Start();

                    if ((Instance.AutoExpandonCursor) && !_isMinimized && _canAutoClose)
                    {
                        AnimateWindowOpacity(Instance.IdleOpacity, Instance.AnimationSpeed);
                        Minimize_MouseLeftButtonDown(null, null);
                        Task.Run(() =>
                        {
                            try
                            {
                                if (!_contextMenuIsOpen)
                                {
                                    _selectedItems.Clear();
                                    foreach (var fileItem in FileItems)
                                    {
                                        fileItem.IsSelected = false;
                                        fileItem.Background = Brushes.Transparent;
                                    }
                                }
                            }
                            catch { }
                        });
                    }
                    else
                    {
                        AnimateWindowOpacity(Instance.IdleOpacity, Instance.AnimationSpeed);
                    }
                }
                if (!_mouseIsOver)
                {
                    timer.Stop();
                }
            };
            timer.Start();
        }
        private void HandleRightClick(Window root, IntPtr lParam)
        {
            POINT pt = new POINT
            {
                X = (short)(lParam.ToInt32() & 0xFFFF),
                Y = (short)((lParam.ToInt32() >> 16) & 0xFFFF)
            };

            System.Windows.Point relativePt = root.PointFromScreen(new System.Windows.Point(pt.X, pt.Y));

            if (root.InputHitTest(relativePt) is DependencyObject hit)
            {
                var listView = FindParentOrChild<ListView>(hit);
                if (listView != null)
                {
                    var mouseArgs = new MouseButtonEventArgs(Mouse.PrimaryDevice, Environment.TickCount, MouseButton.Right)
                    {
                        RoutedEvent = UIElement.MouseRightButtonUpEvent,
                        Source = listView
                    };
                    FileListView_MouseRightButtonUp(listView, mouseArgs);
                }
            }
        }
        public void FirstRowByLastAccessed(ObservableCollection<FileItem> items, List<string> lastAccessedFiles, int topN)
        {
            var wrapPanel = FindParentOrChild<WrapPanel>(FileWrapPanel);
            if (wrapPanel != null)
            {
                double itemWidth = wrapPanel.ItemWidth;
                ItemPerRow = (int)((this.Width) / itemWidth);
            }
            if (items == null || items.Count == 0 || lastAccessedFiles == null || lastAccessedFiles.Count == 0 || topN <= 0)
                return;
            var fileLookup = items
                .Where(i => i.FullPath != null)
                .GroupBy(i => GetFileId(i.FullPath!).ToString())
                .ToDictionary(g => g.Key, g => g.ToList());

            var topIds = lastAccessedFiles
                .Where(id => fileLookup.ContainsKey(id))
                .Take(topN)
                .ToList();

            int insertIndex = 0;
            foreach (var id in topIds)
            {
                foreach (var item in fileLookup[id])
                {
                    int oldIndex = items.IndexOf(item);
                    if (oldIndex >= 0 && oldIndex != insertIndex)
                        items.Move(oldIndex, insertIndex);
                    insertIndex++;
                }
            }
            var remainingItems = new ObservableCollection<FileItem>(items.Skip(insertIndex));
            var sortedRemaining = SortFileItems(remainingItems, (int)Instance.SortBy, Instance.FolderOrder);
            for (int i = 0; i < sortedRemaining.Count; i++)
            {
                int oldIndex = items.IndexOf(sortedRemaining[i]);
                if (oldIndex >= 0 && oldIndex != insertIndex + i)
                    items.Move(oldIndex, insertIndex + i);
            }
        }
        private IntPtr WndProc(IntPtr hWnd, int msg, IntPtr wParam, IntPtr lParam, ref bool handled)
        {
            if (!(HwndSource.FromHwnd(hWnd).RootVisual is Window rootVisual))
                return IntPtr.Zero;
          
            if (msg == 0x0005) // WM_SIZE
            {
                if (_dragMovingWinddow)
                {
                    handled = true;
                    return -1;
                }
            }
            if (_isLeftButtonDown && _bringForwardForMove && msg == 0x0003) // WM_MOVE
            {
                BringFrameToFront(new WindowInteropHelper(this).Handle, true);
                _bringForwardForMove = false;
                return -1;
            }
            if (msg == 0x020A && (GetAsyncKeyState(0x11) & 0x8000) != 0) // WM_MOUSEWHEEL && control down
            {
                _changeIconSizeCts.Cancel();
                _changeIconSizeCts = new CancellationTokenSource();
                var token = _changeIconSizeCts.Token;
                int delta = (short)((int)wParam >> 16);
                if (delta < 0) Instance.IconSize -= 4;
                else if (delta > 0) Instance.IconSize += 4;
                Task.Run(async () =>
                {
                    await Task.Delay(500, token);
                    if (!token.IsCancellationRequested)
                    {
                        Dispatcher.Invoke(() =>
                        {
                            LoadingProgressRingFade(true);
                        });
                        foreach (var item in FileItems)
                        {
                            item.Thumbnail = await GetThumbnailAsync(item.FullPath!);
                        }
                        Dispatcher.Invoke(() =>
                        {
                            FileWrapPanel.Items.Refresh();
                            Task.Run(async () =>
                            {
                                await Task.Delay(200, token);
                                Dispatcher.Invoke(() =>
                                {
                                    LoadingProgressRingFade(false);
                                });
                            });
                        });
                    }
                });
                handled = true;
                return 4;
            }


            else if (msg == 0x020A && Mouse.GetPosition(this).Y <= titleBar.Height)
            {

                int delta = (short)((int)wParam >> 16);
                if (delta > 0 && !_isTopmost)
                {
                    // TODO: redo this when proper PDI scaling is merged
                    Debug.WriteLine("Bring frame above other windows");
                    _isTopmost = true;
                    var dpi = VisualTreeHelper.GetDpi(this);

                    SetParent(new WindowInteropHelper(this).Handle, IntPtr.Zero);

                    SetWindowPos(new WindowInteropHelper(this).Handle,
                        IntPtr.Zero,
                        (int)(Instance.PosX * dpi.DpiScaleX),
                         (int)(Instance.PosY * dpi.DpiScaleY),
                        0,
                        0,
                        SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);

                    this.Height = Instance.Height;
                    this.Width = Instance.Width;

                    BackgroundType(true);
                    this.Activate();
                    this.Show();
                    this.Topmost = true;
                }
                else if (delta < 0 && _isTopmost)
                {
                    Debug.WriteLine("Push frame behind other windows");
                    _isTopmost = false;
                    this.Topmost = false;
                    BackgroundType(false);
                    SetAsDesktopChild();

                    HandleWindowMove(true);
                    // force redraw
                    this.Width += 1;
                    this.Width -= 1;
                }
            }

            if (msg == 0x0201) // WM_LBUTTONDOWN
            {
                _isLeftButtonDown = true;
                _bringForwardForMove = true;
                _grabbedOnLeft = Mouse.GetPosition(this).X < this.Width / 2;
            }
            if (msg == 0x0202) // WM_LBUTTONUP
            {
                _isLeftButtonDown = false;
                _bringForwardForMove = false;
            }
            if (msg == 0x0205) // WM_RBUTTONUP
            {
                HandleRightClick(rootVisual, lParam);
                handled = true;
            }
            if (msg == 0x0205) // WM_RBUTTONUP
            {
                int x = lParam.ToInt32() & 0xFFFF;
                int y = (lParam.ToInt32() >> 16) & 0xFFFF;
                var screenPoint = new System.Windows.Point(x, y);
                var relativePoint = FileWrapPanel.PointFromScreen(screenPoint);
                if (VisualTreeHelper.HitTest(FileWrapPanel, relativePoint) == null)
                {
                    var curPos = System.Windows.Forms.Cursor.Position;
                    try
                    {
                        var windowHelper = new WindowInteropHelper(this);
                        Point cursorPosition = System.Windows.Forms.Cursor.Position;
                        System.Windows.Point wpfPoint = new System.Windows.Point(cursorPosition.X, cursorPosition.Y);
                        Point drawingPoint = new Point((int)wpfPoint.X, (int)wpfPoint.Y);
                        DirectoryInfo folder = new DirectoryInfo(_currentFolderPath);
                        _contextMenuIsOpen = true;
                        scm.ContextMenuClosed += () =>
                        {
                            _contextMenuIsOpen = false;
                        };
                        if (_itemCurrentlyRenaming != null)
                        {
                            _itemCurrentlyRenaming.IsRenaming = false;
                        }
                        scm.ShowContextMenu(windowHelper.Handle, new DirectoryInfo(_currentFolderPath), drawingPoint, true);
                        handled = true;
                    }
                    catch
                    {
                    }

                }
            }
            if (msg == 0x0100 && wParam.ToInt32() == 0x71) // F2 down
            {
                if (_itemUnderCursor != null)
                {
                    if (_itemCurrentlyRenaming != null)
                    {
                        _itemCurrentlyRenaming.IsRenaming = false;
                    }
                    _itemCurrentlyRenaming = _itemUnderCursor;
                    _itemCurrentlyRenaming.IsRenaming = true;
                    DependencyObject container;
                    if (Instance.ShowInGrid)
                    {
                        container = FileWrapPanel.ItemContainerGenerator.ContainerFromItem(_itemCurrentlyRenaming);
                    }
                    else
                    {
                        container = FileListView.ItemContainerGenerator.ContainerFromItem(_itemCurrentlyRenaming);
                        FileListView.SelectedItem = _itemCurrentlyRenaming;
                    }
                    var renameTextBox = FindParentOrChild<TextBox>(container);
                    renameTextBox!.Text = _itemCurrentlyRenaming.Name;
                    _isRenaming = true;
                    renameTextBox.Focus();

                    var text = renameTextBox.Text;
                    var dotIndex = text.LastIndexOf('.');
                    if (dotIndex <= 0) renameTextBox.SelectAll();
                    else renameTextBox.Select(0, dotIndex);
                }
            }

            if (msg == 0x0214) // WM_SIZING
            {
                int edge = wParam.ToInt32();
                if (_isMinimized && (edge != 1 && edge != 2)) // block resizing except left or right edges
                {
                    var hwnd = new WindowInteropHelper(this).Handle;
                    Interop.RECT currentRect;
                    Interop.GetWindowRect(hwnd, out currentRect);
                    Marshal.StructureToPtr(currentRect, lParam, true);
                    handled = true;
                    return IntPtr.Zero;
                }
                Interop.RECT rect = (Interop.RECT)Marshal.PtrToStructure(lParam, typeof(Interop.RECT));

                Instance.PosX = this.Left;
                Instance.PosY = this.Top;

                Instance.Width = this.Width;
                double height = rect.Bottom - rect.Top;
                if (height <= 102 && !_isMinimized)
                {
                    this.Height = 102;
                    rect.Bottom = rect.Top + 102;
                    Marshal.StructureToPtr(rect, lParam, true);
                    handled = true;
                    return (IntPtr)4;
                }
                else if (!_isMinimized && this.ActualHeight != titleBar.Height && _canAnimate)
                {
                    Instance.Height = this.ActualHeight;
                }

                if (Instance.LastAccesedToFirstRow)
                {
                    var wrapPanel = FindParentOrChild<WrapPanel>(FileWrapPanel);
                    if (wrapPanel != null)
                    {
                        double width = rect.Right - rect.Left;
                        double newWidth = rect.Right - rect.Left;

                        if (Instance.SnapWidthToIconWidth)
                        {
                            newWidth = Math.Round(width / wrapPanel.ItemWidth) * wrapPanel.ItemWidth + 4; // +4 margin
                            if (Instance.SnapWidthToIconWidth)
                            {
                                FileWrapPanel.Margin = new Thickness(6, 5, 0, 5);
                                newWidth += 15;
                            }
                        }
                        if (!Instance.SnapWidthToIconWidth)
                        {
                            FileWrapPanel.Margin = new Thickness(0, 0, 0, 0);
                        }
                        int newItemPerRow = (int)Math.Floor(newWidth / wrapPanel.ItemWidth);
                        if (_previousItemPerRow != newItemPerRow)
                        {
                            ItemPerRow = newItemPerRow;
                            FirstRowByLastAccessed(FileItems, Instance.LastAccessedFiles, ItemPerRow);
                            _previousItemPerRow = newItemPerRow;
                        }
                    }
                }

                if (Instance.SnapWidthToIconWidth)
                {
                    double width = rect.Right - rect.Left;
                    var item = FindParentOrChild<WrapPanel>(FileWrapPanel);
                    double newWidth = Math.Round(width / item.ItemWidth) * item.ItemWidth + 4; // +4 margin

                    if (Instance.SnapWidthToIconWidth_PlusScrollbarWidth)
                    {
                        newWidth += 15;
                        FileWrapPanel.Margin = new Thickness(6, 5, 0, 5);
                    }
                    else
                    {
                        FileWrapPanel.Margin = new Thickness(0, 0, 0, 0);
                    }
                    if (width != newWidth)
                    {
                        int diff = (int)(newWidth - width);
                        int w = (int)wParam;

                        if (w == 1 || w == 5 || w == 7) // left sides
                        {
                            rect.Left -= diff;
                        }
                        if (w == 2 || w == 6 || w == 8) // right sides
                        {
                            rect.Right += diff;
                        }

                        Marshal.StructureToPtr(rect, lParam, true);
                        Instance.Width = this.Width;
                    }
                }
            }

            if (msg == 0x0005 && _isOnBottom) // WM_SIZE
            {
                double newHeight = (lParam.ToInt32() >> 16) & 0xFFFF;
                if (_previousHeight != -1 && _previousHeight != newHeight)
                {
                    IntPtr hwnd = new WindowInteropHelper(this).Handle;

                    var workingArea = Screen.FromPoint(System.Windows.Forms.Control.MousePosition).WorkingArea;

                    Interop.GetWindowRect(hwnd, out RECT windowRect);
                    POINT pt = new POINT { X = windowRect.Left, Y = windowRect.Top };
                    ScreenToClient(GetParent(hwnd), ref pt);
                    double delta = newHeight - _previousHeight;
                    int newTop = (int)((pt.Y - delta) - windowRect.Bottom <= workingArea.Bottom ?
                        (int)(pt.Y -= (int)delta) :
                        Instance.Height - workingArea.Bottom - titleBar.Height);

                    if (delta > 0) // UP
                    {
                        Application.Current.Dispatcher.BeginInvoke(() =>
                        {
                            Interop.SetWindowPos(hwnd, IntPtr.Zero, pt.X,
                                    newTop,
                                    0, 0,
                                   SWP_NOSIZE
                                  );

                        }, DispatcherPriority.Normal);
                    }
                    else
                    {
                        Interop.SetWindowPos(hwnd, IntPtr.Zero, pt.X,
                                newTop,
                                0, 0,
                               SWP_NOSIZE | SWP_NOACTIVATE | SWP_NOREDRAW
                              );
                    }
                    if (this.Top + titleBar.Height > workingArea.Bottom)
                    {
                        // this.Top = workingArea.Bottom - 30;
                        _didFixIsOnBottom = true;
                        Interop.SetWindowPos(hwnd, IntPtr.Zero, pt.X,
                              (int)(workingArea.Bottom - titleBar.Height),
                              0, 0,
                             SWP_NOSIZE | SWP_NOACTIVATE | SWP_NOREDRAW
                            );
                    }
                    if (_fixIsOnBottomInit && pt.Y + this.Height != workingArea.Bottom)
                    {
                        Interop.SetWindowPos(hwnd, IntPtr.Zero, pt.X,
                           (int)(workingArea.Bottom - this.Height + 1), // +1 pixel because otherwise it hovers  by 1 px above the desktop
                           0, 0,
                          SWP_NOSIZE | SWP_NOACTIVATE | SWP_NOREDRAW
                         );
                    }
                }
                _previousHeight = newHeight;
                return 4;
            }

            if (msg == 70)
            {
                Interop.WINDOWPOS structure = Marshal.PtrToStructure<Interop.WINDOWPOS>(lParam);
                structure.flags |= 4U;
                Marshal.StructureToPtr<Interop.WINDOWPOS>(structure, lParam, false);
            }
            if (msg == 0x0003 &&  // WM_MOVE
                ((GetAsyncKeyState(0xA4) & 0x8000) == 0 && (GetAsyncKeyState(0xA5) & 0x8000) == 0)) // left and right alt isn't down
            {
                _isIngrid = false;

                HandleWindowMove(false);
                if (WonRight != null)
                {
                    WonRight.HandleWindowMove(false);
                }
                if (WonLeft != null)
                {
                    WonLeft.HandleWindowMove(false);
                }
            }
            if (_isLeftButtonDown &&
                ((GetAsyncKeyState(0xA4) & 0x8000) != 0 || (GetAsyncKeyState(0xA5) & 0x8000) != 0) && // left or right is alt down
                msg == 0x0003) // WM_MOVE
            {
                SnapToGrid();
            }

            return IntPtr.Zero;
        }
        private void SnapToGrid()
        {
            IntPtr hwnd = new WindowInteropHelper(this).Handle;

            Interop.RECT windowRect;
            Interop.GetWindowRect(hwnd, out windowRect);

            int windowLeft = windowRect.Left;
            int windowTop = windowRect.Top;
            int windowRight = windowRect.Right;
            int windowBottom = windowRect.Bottom;

            var mainWindow = Application.Current.MainWindow as MainWindow;
            if (mainWindow == null) return;

            int newWindowLeft = windowLeft;
            int newWindowTop = windowTop;
            int newWindowBottom = windowBottom;
            foreach (var otherWindow in MainWindow._controller._subWindows)
            {
                if (otherWindow == this) continue;

                IntPtr otherHwnd = new WindowInteropHelper(otherWindow).Handle;
                Interop.RECT otherWindowRect;
                Interop.GetWindowRect(otherHwnd, out otherWindowRect);

                int otherLeft = otherWindowRect.Left;
                int otherTop = otherWindowRect.Top;
                int otherRight = otherWindowRect.Right;
                int otherBottom = otherWindowRect.Bottom;
                bool didSnap = false;
                if (Math.Abs(windowLeft - otherRight) <= _gridSnapDistance && Math.Abs(windowTop - otherTop) <= titleBar.Height)
                {
                    newWindowLeft = otherRight + _gridSnapDistance;
                    newWindowTop = otherTop;
                    if (_grabbedOnLeft) didSnap = true;
                }
                else if (Math.Abs(windowRight - otherLeft) <= _gridSnapDistance && Math.Abs(windowTop - otherTop) <= titleBar.Height)
                {
                    newWindowLeft = otherLeft - (windowRight - windowLeft) - _gridSnapDistance;
                    newWindowTop = otherTop;
                    if (_grabbedOnLeft) didSnap = true;
                }
                if (_grabbedOnLeft && !didSnap)
                {
                    if (Math.Abs(windowTop - otherBottom) <= _gridSnapDistance && Math.Abs(windowLeft - otherLeft) <= _snapDistance)
                    {
                        newWindowTop = otherBottom + _gridSnapDistance;
                        newWindowLeft = otherLeft;

                    }
                    else if (Math.Abs(windowBottom - otherTop) <= _gridSnapDistance && Math.Abs(windowLeft - otherLeft) <= _snapDistance)
                    {
                        newWindowTop = otherTop - (windowBottom - windowTop) - _gridSnapDistance;
                        newWindowLeft = otherLeft;
                    }
                }

                if (Math.Abs(windowRight - otherRight) <= _gridSnapDistance && Math.Abs(windowTop - otherBottom) <= _snapDistance)
                {
                    newWindowTop = otherBottom + _gridSnapDistance;
                    newWindowLeft = otherRight - (windowRight - windowLeft);
                }
                else if (Math.Abs(windowRight - otherRight) <= _gridSnapDistance && Math.Abs(windowBottom - otherTop) <= _snapDistance)
                {
                    newWindowTop = otherTop - (windowBottom - windowTop) - _gridSnapDistance;
                    newWindowLeft = otherRight - (windowRight - windowLeft);
                }
            }

            if (newWindowLeft != windowLeft || newWindowTop != windowTop || newWindowBottom != windowBottom)
            {
                POINT pt = new POINT { X = newWindowLeft, Y = newWindowTop };
                ScreenToClient(GetParent(hwnd), ref pt);
                SetWindowPos(hwnd, IntPtr.Zero, pt.X, pt.Y, 0, 0,
                             SWP_NOZORDER | SWP_NOSIZE | SWP_NOACTIVATE);

                HandleWindowMove(false);
                _isIngrid = true;
            }
            else
            {
                _isIngrid = false;
            }
        }
        public void HandleWindowMove(bool initWindow)
        {
            if (_isTopmost)
            {
                return;
            }
            Interop.RECT windowRect;
            IntPtr hwnd = new WindowInteropHelper(this).Handle;
            Interop.GetWindowRect(hwnd, out windowRect);

            int windowLeft = windowRect.Left;
            int windowTop = windowRect.Top;
            int windowRight = windowRect.Right;
            int windowBottom = windowRect.Bottom;

            var mainWindow = Application.Current.MainWindow as MainWindow;
            if (mainWindow == null) return;

            int newWindowLeft = windowLeft;
            int newWindowTop = windowTop;
            int newWindowBottom = windowBottom;


            var workingArea = Screen.FromPoint(System.Windows.Forms.Control.MousePosition).WorkingArea;

            //if (Math.Abs(windowLeft - workingArea.Left) <= _snapDistance)
            //{
            //    newWindowLeft = (int)workingArea.Left;
            //    _isOnEdge = true;
            //}
            //else if (Math.Abs(windowRight - workingArea.Right) <= _snapDistance)
            //{
            //    newWindowLeft = (int)(workingArea.Right - (windowRight - windowLeft));
            //    _isOnEdge = true;
            //}
            //else
            //{
            //    _isOnEdge = false;
            //}
            // Debug.WriteLine(windowBottom + " " + (workingArea.Bottom <= windowBottom));
            if (_isLeftButtonDown || initWindow)
            {
                POINT pt = new POINT { X = newWindowLeft, Y = newWindowTop };
                ScreenToClient(GetParent(hwnd), ref pt);
                windowTop = pt.Y;
                windowBottom = pt.Y + (windowBottom - windowTop);
                if (Math.Abs(windowTop - workingArea.Top) <= _snapDistance)
                {
                    newWindowTop = (int)workingArea.Top;
                    WindowBackground.CornerRadius = new CornerRadius(0, 0, 5, 5);
                    _isOnBottom = false;
                    _isOnTop = true;
                }
                else if (Math.Abs(windowBottom - workingArea.Bottom) - 2 <= _snapDistance
                   || (Math.Abs(windowBottom - workingArea.Bottom + Instance.Height - titleBar.Height) - 2 <= _snapDistance && initWindow)
                   )
                {
                    newWindowTop = (int)(workingArea.Bottom - (windowBottom - windowTop));
                    newWindowBottom = (int)workingArea.Bottom;
                    WindowBackground.CornerRadius = new CornerRadius(5, 5, 0, 0);
                    _isOnTop = false;
                    _isOnBottom = true;
                }
                else if (!_isOnBottom)
                {
                    _isOnTop = false;
                    WindowBackground.CornerRadius = new CornerRadius(5);
                    titleBar.CornerRadius = new CornerRadius(5, 5, 0, 0);
                }
                if (workingArea.Bottom <= windowBottom)
                {
                    newWindowBottom = (int)workingArea.Bottom;
                    WindowBackground.CornerRadius = new CornerRadius(5, 5, 0, 0);
                    _isOnTop = false;
                    _isOnBottom = true;
                }
                else if (_isLeftButtonDown)
                {
                    _isOnBottom = false;
                }
                if (Math.Abs(windowLeft - workingArea.Left) <= _snapDistance)
                {
                    newWindowLeft = workingArea.Left;
                }
                else if (Math.Abs(workingArea.Right - windowRight) <= _snapDistance)
                {
                    newWindowLeft = (int)(workingArea.Right - this.ActualWidth);
                }
            }
            neighborFrameCount = 0;

            bool onLeft = false;
            bool onRight = false;
            foreach (var otherWindow in MainWindow._controller._subWindows)
            {
                if (otherWindow == this) continue;
                if (otherWindow._isTopmost) // prevent unintentional dragging of neighboring window
                {
                    return;
                }
                IntPtr otherHwnd = new WindowInteropHelper(otherWindow).Handle;
                Interop.RECT otherWindowRect;
                Interop.GetWindowRect(otherHwnd, out otherWindowRect);

                int otherLeft = otherWindowRect.Left;
                int otherTop = otherWindowRect.Top;
                int otherRight = otherWindowRect.Right;
                int otherBottom = otherWindowRect.Bottom;

                if (Math.Abs(windowLeft - otherRight) <= _snapDistance && Math.Abs(windowTop - otherTop) <= _snapDistance)
                {
                    newWindowLeft = otherRight;
                    newWindowTop = otherTop;
                    WonRight = otherWindow;
                    onLeft = true;
                    neighborFrameCount++;
                }
                else if (Math.Abs(windowRight - otherLeft) <= _snapDistance && Math.Abs(windowTop - otherTop) <= _snapDistance)
                {
                    newWindowLeft = otherLeft - (windowRight - windowLeft);
                    newWindowTop = otherTop;
                    WonLeft = otherWindow;
                    onRight = true;
                    neighborFrameCount++;
                }

                if (Math.Abs(windowLeft - otherRight) <= _snapDistance && Math.Abs(windowBottom - otherBottom) <= _snapDistance)
                {
                    newWindowLeft = otherRight;
                    newWindowBottom = (int)workingArea.Bottom;
                    WonRight = otherWindow;
                    onLeft = true;
                    neighborFrameCount++;
                }
                else if (Math.Abs(windowRight - otherLeft) <= _snapDistance && Math.Abs(windowBottom - otherBottom) <= _snapDistance)
                {
                    newWindowLeft = otherLeft - (windowRight - windowLeft);
                    newWindowBottom = (int)workingArea.Bottom;
                    WonLeft = otherWindow;
                    onRight = true;
                    neighborFrameCount++;
                }

                if (Math.Abs(windowTop - otherBottom) <= _snapDistance && Math.Abs(windowLeft - otherLeft) <= _snapDistance)
                {
                    newWindowTop = otherBottom;
                }
                else if (Math.Abs(windowBottom - otherTop) <= _snapDistance && Math.Abs(windowLeft - otherLeft) <= _snapDistance)
                {
                    newWindowTop = otherTop - (windowBottom - windowTop);
                }
            }
            if (neighborFrameCount >= 2)
            {
                WindowBackground.CornerRadius = new CornerRadius(0);
                titleBar.CornerRadius = new CornerRadius(0);
            }
            if (neighborFrameCount == 0)
            {
                if (WonRight != null && !onLeft)
                {
                    if (!WonRight._isMinimized)
                    {
                        WonRight.WindowBorder.CornerRadius = new CornerRadius(
                            topLeft: WonRight._isOnTop ? 0 : WonRight.WonRight == null ? 5 : 0,
                            topRight: WonRight._isOnTop ? 0 : (WonRight._isOnBottom ? 0 : 5),
                            bottomRight: WonRight._isOnBottom ? 0 : 5,
                            bottomLeft: WonRight._isOnBottom ? 0 : 5
                        );
                        WonRight.titleBar.CornerRadius = new CornerRadius(
                            topLeft: WonRight.WindowBorder.CornerRadius.TopLeft,
                            topRight: WonRight.WindowBorder.CornerRadius.TopRight,
                            bottomRight: 0,
                            bottomLeft: 0
                        );
                    }
                    else
                    {
                        WonRight.WindowBorder.CornerRadius = new CornerRadius(
                            topLeft: WonRight._isOnTop ? 0 : WonRight.WonRight == null ? 5 : 0,
                            topRight: WonRight._isOnTop ? 0 : (WonRight._isOnBottom ? 0 : 5),
                            bottomRight: WonRight._isOnBottom ? 0 : 5,
                            bottomLeft: WonRight.WonRight == null ? (WonRight._isOnBottom ? 0 : 5) : 0
                        );
                        WonRight.titleBar.CornerRadius = WonRight.WindowBorder.CornerRadius;

                    }
                    WonRight.WindowBackground.CornerRadius = WonRight.WindowBorder.CornerRadius;
                    WonRight.WonLeft = null;
                    WonRight = null;
                }
                if (WonLeft != null && !onRight)
                {
                    if (!WonLeft._isMinimized)
                    {
                        WonLeft.WindowBorder.CornerRadius = new CornerRadius(
                            topLeft: WonLeft._isOnTop ? 0 : (WonLeft._isOnBottom ? 0 : 5),
                            topRight: WonLeft._isOnTop ? 0 : WonLeft.WonLeft == null ? 5 : 0,
                            bottomRight: WonLeft._isOnBottom ? 0 : 5,
                            bottomLeft: WonLeft._isOnBottom ? 0 : 5
                        );
                        WonLeft.titleBar.CornerRadius = new CornerRadius(
                            topLeft: WonLeft.WindowBorder.CornerRadius.TopLeft,
                            topRight: WonLeft.WindowBorder.CornerRadius.TopRight,
                            bottomRight: 0,
                            bottomLeft: 0
                        );
                    }
                    else
                    {
                        WonLeft.WindowBorder.CornerRadius = new CornerRadius(
                            topLeft: WonLeft._isOnTop ? 0 : (WonLeft._isOnBottom ? 0 : 5),
                            topRight: WonLeft._isOnTop ? 0 : WonLeft.WonLeft == null ? 5 : 0,
                            bottomRight: WonLeft.WonLeft == null ? (WonLeft._isOnBottom ? 0 : 5) : 0,
                            bottomLeft: WonLeft._isOnBottom ? 0 : 5
                        );
                        WonLeft.titleBar.CornerRadius = WonLeft.WindowBorder.CornerRadius;

                    }
                    WonLeft.WindowBackground.CornerRadius = WonLeft.WindowBorder.CornerRadius;
                    WonLeft.WonRight = null;
                    WonLeft = null;
                }

            }
            if (!_isMinimized)
            {
                if (_isOnBottom)
                {
                    WindowBorder.CornerRadius = new CornerRadius(
                        topLeft: 5,
                        topRight: 5,
                        bottomRight: 0,
                        bottomLeft: 0
                    );
                    WindowBackground.CornerRadius = WindowBorder.CornerRadius;
                    titleBar.CornerRadius = new CornerRadius(
                        topLeft: WindowBorder.CornerRadius.TopLeft,
                        topRight: WindowBorder.CornerRadius.TopRight,
                        bottomRight: 5,
                        bottomLeft: 5
                    );
                }
                else
                {
                    WindowBorder.CornerRadius = new CornerRadius(
                        topLeft: _isOnTop ? 0 : WonRight == null ? 5 : 0,
                        topRight: _isOnTop ? 0 : WonLeft == null ? 5 : 0,
                        bottomRight: 5,
                        bottomLeft: 5
                    );
                    WindowBackground.CornerRadius = WindowBorder.CornerRadius;
                    titleBar.CornerRadius = new CornerRadius(
                        topLeft: WindowBorder.CornerRadius.TopLeft,
                        topRight: WindowBorder.CornerRadius.TopRight,
                        bottomRight: 0,
                        bottomLeft: 0
                    );
                }
            }
            else
            {
                if (_isOnBottom)
                {
                    WindowBorder.CornerRadius = new CornerRadius(
                        topLeft: WonRight == null ? 5 : 0,
                        topRight: WonLeft == null ? 5 : 0,
                        bottomRight: 0,
                        bottomLeft: 0
                   );
                }
                else
                {
                    WindowBorder.CornerRadius = new CornerRadius(
                        topLeft: _isOnTop ? 0 : WonRight == null ? 5 : 0,
                        topRight: _isOnTop ? 0 : WonLeft == null ? 5 : 0,
                        bottomRight: WonLeft == null ? 5 : 0,
                        bottomLeft: WonRight == null ? 5 : 0
                    );
                }
                WindowBackground.CornerRadius = WindowBorder.CornerRadius;
                titleBar.CornerRadius = WindowBorder.CornerRadius;
            }



            if ((initWindow && _isOnBottom) ||
                (!_isIngrid && !_isOnBottom
                    && (newWindowLeft != windowLeft || newWindowTop != windowTop || newWindowBottom != windowBottom && !_isLeftButtonDown)))
            {
                POINT pt = new POINT { X = newWindowLeft, Y = newWindowTop };
                ScreenToClient(GetParent(hwnd), ref pt);
                SetWindowPos(hwnd, IntPtr.Zero, pt.X, pt.Y, 0, 0,
                             SWP_NOZORDER | SWP_NOSIZE | SWP_NOACTIVATE);
            }

        }

        public void SetCornerRadius(Border border, double topLeft, double topRight, double bottomLeft, double bottomRight)
        {
            border.CornerRadius = new CornerRadius(topLeft, topRight, bottomLeft, bottomRight);
        }

        private void SetAsDesktopChild()
        {
            while (true)
            {
                while (shellView == IntPtr.Zero)
                {
                    EnumWindows((tophandle, _) =>
                    {
                        IntPtr shellViewIntPtr = FindWindowEx(tophandle, IntPtr.Zero, "SHELLDLL_DefView", null);
                        if (shellViewIntPtr != IntPtr.Zero)
                        {
                            shellView = shellViewIntPtr;
                            return false;
                        }
                        return true;
                    }, IntPtr.Zero);
                }
                if (shellView == IntPtr.Zero) Thread.Sleep(1000);
                else break;
            }
            if (shellView == IntPtr.Zero) throw new InvalidOperationException("SHELLDLL_DefView not found.");

            var interopHelper = new WindowInteropHelper(this);
            interopHelper.EnsureHandle();
            IntPtr hwnd = interopHelper.Handle;
            SetParent(hwnd, shellView);

            int style = (int)GetWindowLong(hwnd, GWL_STYLE);
            style &= ~WS_POPUP; // remove flag, to make sure it doesn't interfere
            style |= WS_CHILD; // add flag
            SetWindowLong(hwnd, GWL_STYLE, style);

            // convert coords to parent-relative coords
            uint dpi = GetDpiForWindow(hwnd);
            _windowsScalingFactor = dpi / 96.0;
            POINT pt = new POINT
            {
                X = (int)(Instance.PosX * _windowsScalingFactor),
                Y = (int)(Instance.PosY * _windowsScalingFactor)
            };
            ScreenToClient(shellView, ref pt);

            SetWindowPos(hwnd, IntPtr.Zero,
                         pt.X, pt.Y,
                         0, 0,
                         SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE | SWP_SHOWWINDOW);
        }

        public async Task AdjustPositionAsync()
        {
            _adjustPositionCts?.Cancel();
            if (isMouseDown) return;

            _adjustPositionCts = new CancellationTokenSource();
            var token = _adjustPositionCts.Token;
            var interopHelper = new WindowInteropHelper(this);
            interopHelper.EnsureHandle();
            IntPtr hwnd = interopHelper.Handle;
            double posX = Instance.PosX;
            double posY = Instance.PosY;

            try
            {
                await Task.Run(() =>
                {
                    if (token.IsCancellationRequested) return;

                    uint dpi = GetDpiForWindow(hwnd);
                    _windowsScalingFactor = dpi / 96.0;

                    POINT pt = new POINT
                    {
                        X = (int)(posX * _windowsScalingFactor),
                        Y = (int)(posY * _windowsScalingFactor)
                    };

                    if (token.IsCancellationRequested) return;
                    ScreenToClient(shellView, ref pt);

                    SetWindowPos(hwnd, IntPtr.Zero,
                                 pt.X, pt.Y,
                                (int)Instance.Width, (int)Instance.Height,
                                  SWP_NOZORDER | SWP_NOACTIVATE | SWP_SHOWWINDOW);
                }, token);
            }
            catch { }
        }
        public async void AdjustPosition()
        {
            SetParent(hwnd, IntPtr.Zero);
            SetAsDesktopChild();
            if (Instance.Minimized)
            {
                this.Height = titleBar.Height;
            }
            var interopHelper = new WindowInteropHelper(this);
            interopHelper.EnsureHandle();
            IntPtr _hwnd = interopHelper.Handle;
            double currentScale = GetDpiForWindow(_hwnd) / 96.0;
            if (_windowsScalingFactor != currentScale)
            {
                _windowsScalingFactor = currentScale;
                foreach (var item in FileItems)
                {
                    item.Thumbnail = await GetThumbnailAsync(item.FullPath!);
                }
            }
        }

        public void SetAsToolWindow()
        {
            WindowInteropHelper wih = new WindowInteropHelper(this);
            IntPtr dwNew = new IntPtr(((long)Interop.GetWindowLong(wih.Handle, Interop.GWL_EXSTYLE).ToInt32() | 128L | 0x00200000L) & 4294705151L);
            Interop.SetWindowLong((nint)new HandleRef(this, wih.Handle), Interop.GWL_EXSTYLE, dwNew);
        }
        public void SetNoActivate()
        {
            if (_isTopmost)
            {
                return;
            }
            IntPtr hwnd = new WindowInteropHelper(this).Handle;
            IntPtr style = Interop.GetWindowLong(hwnd, Interop.GWL_EXSTYLE);
            IntPtr newStyle = new IntPtr(style.ToInt64() | Interop.WS_EX_NOACTIVATE);
            Interop.SetWindowLong(hwnd, Interop.GWL_EXSTYLE, newStyle);
        }
        private void Window_KeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (_isRenaming)
            {
                return;
            }

            if (FilterTextBox.IsFocused)
            {
                if (e.Key == Key.Escape)
                {
                    FilterTextBox.Text = null;
                    this.Focus();
                    e.Handled = true;
                }
                return;
            }

            if (e.Key == Key.Delete)
            {
                var selected = GetSelectedFileItems();
                if (selected.Count > 0)
                {
                    e.Handled = true;
                    bool permanent = (Keyboard.Modifiers & ModifierKeys.Shift) == ModifierKeys.Shift;
                    DeleteSelectedFiles(selected, permanent);
                }
                return;
            }

            if ((Keyboard.Modifiers & ModifierKeys.Control) == ModifierKeys.Control && e.Key == Key.A)
            {
                _selectedItems.Clear();
                foreach (var item in FileItems)
                {
                    item.IsSelected = true;
                    _selectedItems.Add(item);
                }
                if (FileListView != null)
                {
                    FileListView.SelectAll();
                }
                e.Handled = true;
                return;
            }

            if (e.Key == Key.Escape || !_mouseIsOver)
            {
                FilterTextBox.Text = null;
            }
            else
            {
                Search.Opacity = 0;
                Search.Visibility = Visibility.Visible;
            }
            FilterTextBox.Focus();
            return;
        }

        private List<FileItem> GetSelectedFileItems()
        {
            var list = new HashSet<FileItem>();

            foreach (var item in _selectedItems)
            {
                if (item.IsSelected)
                {
                    list.Add(item);
                }
            }

            foreach (var item in FileItems)
            {
                if (item.IsSelected)
                {
                    list.Add(item);
                }
            }

            if (FileListView?.SelectedItems != null)
            {
                foreach (var obj in FileListView.SelectedItems)
                {
                    if (obj is FileItem fileItem)
                    {
                        list.Add(fileItem);
                    }
                }
            }

            return list.Where(item => !string.IsNullOrEmpty(item.FullPath)).ToList();
        }

        private void DeleteSelectedFiles(List<FileItem> selected, bool permanent)
        {
            if (selected == null || selected.Count == 0) return;

            var hwnd = new WindowInteropHelper(this).Handle;
            var paths = selected
                .Select(item => item.FullPath)
                .Where(p => !string.IsNullOrEmpty(p) && (File.Exists(p) || Directory.Exists(p)))
                .ToList();

            if (paths.Count == 0) return;

            bool success = Interop.DeleteFiles(hwnd, paths!, permanent);
            if (success)
            {
                var removedList = selected
                    .Where(item => !string.IsNullOrEmpty(item.FullPath) && !File.Exists(item.FullPath) && !Directory.Exists(item.FullPath))
                    .ToList();

                foreach (var item in removedList)
                {
                    FileItems.Remove(item);
                    _selectedItems.Remove(item);
                }
            }
        }

        private async void FilterTextBox_TextChanged(object sender, TextChangedEventArgs e)
        {
            if (string.IsNullOrEmpty(FilterTextBox.Text))
            {
                Search.Visibility = Visibility.Collapsed;
                title.Visibility = Visibility.Visible;
            }
            else if (_mouseIsOver)
            {
                Search.Opacity = 1;
                Search.Visibility = Visibility.Visible;
                Search.Margin = PathToBackButton.Visibility == Visibility.Visible ?
                    new Thickness(PathToBackButton.Width + 4, 0, 0, 0) : new Thickness(0, 0, 0, 0);
                title.Visibility = Visibility.Collapsed;
            }


            if (_collectionView == null)
                return;

            string filter = _mouseIsOver ? FilterTextBox.Text : "";
            _cts.Cancel();
            _cts = new CancellationTokenSource();
            var token = _cts.Token;

            try
            {
                await Task.Delay(50, token);
                _selectedItems.Clear();
                if (!_contextMenuIsOpen)
                {
                    foreach (var fileItem in FileItems)
                    {
                        fileItem.IsSelected = false;
                        fileItem.Background = Brushes.Transparent;
                    }
                    _selectedItems.Clear();
                }
                string regexPattern = Regex.Escape(filter).Replace("\\*", ".*"); // Escape other regex special chars and replace '*' with '.*'

                var filteredItems = await Task.Run(() =>
                {
                    return new Predicate<object>(item =>
                    {
                        if (token.IsCancellationRequested) return false;
                        var fileItem = item as FileItem;
                        return string.IsNullOrWhiteSpace(filter) ||
                               Regex.IsMatch(fileItem.Name!, regexPattern, RegexOptions.IgnoreCase);
                    });
                }, token);

                if (!token.IsCancellationRequested)
                {
                    await Dispatcher.InvokeAsync(() =>
                    {
                        _collectionView.Filter = filteredItems;
                        _collectionView.Refresh();
                    });
                }
            }
            catch (TaskCanceledException)
            {
            }
        }

        protected override void OnSourceInitialized(EventArgs e)
        {
            base.OnSourceInitialized(e);
            IntPtr hwnd = new WindowInteropHelper(this).Handle;
            int exStyle = (int)Interop.GetWindowLong(hwnd, Interop.GWL_EXSTYLE);
            Interop.SetWindowLong(hwnd, Interop.GWL_EXSTYLE, exStyle | Interop.WS_EX_NOACTIVATE);
            WindowChrome.SetWindowChrome(this, Instance.IsLocked ?
                new WindowChrome
                {
                    ResizeBorderThickness = new Thickness(0),
                    CaptionHeight = 0,
                    CornerRadius = new CornerRadius(0)
                } :
                new WindowChrome
                {
                    GlassFrameThickness = new Thickness(0),
                    CaptionHeight = 0,
                    ResizeBorderThickness = new Thickness(5),
                    CornerRadius = new CornerRadius(0)
                }
            );
            KeepWindowBehind();
            SetAsDesktopChild();
            SetNoActivate();
            SetAsToolWindow();
            HwndSource source = HwndSource.FromHwnd(new WindowInteropHelper(this).Handle);
            source.AddHook(WndProc);
            MouseLeaveWindow(false);
            FileListView.ItemContainerGenerator.StatusChanged += ItemContainerGenerator_StatusChanged;
        }
        private void ItemContainerGenerator_StatusChanged(object sender, EventArgs e)
        {
            if (FileListView.ItemContainerGenerator.Status == GeneratorStatus.ContainersGenerated)
            {
                foreach (var item in FileListView.Items)
                {
                    var container = FileListView.ItemContainerGenerator.ContainerFromItem(item) as ListViewItem;
                    if (container != null)
                    {
                        container.MouseEnter += ListViewItem_MouseEnter;
                        container.MouseLeave += ListViewItem_MouseLeave;
                        container.Selected += ListViewItem_Selected;
                        container.Unselected += ListViewItem_Unselected;
                        container.PreviewMouseUp += FileListView_PreviewMouseUp;
                        container.MouseDoubleClick += FileListView_DoubleClick;
                        container.PreviewMouseDown += FileListView_MouseLeftButtonDown;
                        container.MouseRightButtonUp += FileListView_MouseRightButtonUp;
                    }
                }
            }
        }
        public DeskFrameWindow(Instance instance)
        {
            InitializeComponent();
            this.Language = XmlLanguage.GetLanguage(CultureInfo.CurrentCulture.IetfLanguageTag);
            this.MinWidth = 98;
            this.Loaded += MainWindow_Loaded;
            this.SourceInitialized += MainWindow_SourceInitialized!;
            hwnd = new WindowInteropHelper(this).Handle;
            this.StateChanged += (sender, args) =>
            {
                this.WindowState = WindowState.Normal;
            };

            Instance = instance;

            _grayscaleEffect = (GrayscaleEffect)FindResource("ImageGrayscaleEffect");
            _grayscaleEffect.Strength = Instance.GrayScaleEnabled ? Instance.MaxGrayScaleStrength : 0;

            this.Width = instance.Width;
            this.Opacity = Instance.IdleOpacity;
            _currentFolderPath = instance.Folder;
            _isLocked = instance.IsLocked;
            _oriPosX = (int)instance.PosX;
            _oriPosY = (int)instance.PosY;
            this.Top = instance.PosY;
            this.Left = instance.PosX;

            title.FontSize = Instance.TitleFontSize;
            title.TextWrapping = TextWrapping.Wrap;
            double titleBarHeight = Math.Max(30, Instance.TitleFontSize * 1.5);
            titleBar.Height = titleBarHeight;

            double scrollViewerMargin = titleBarHeight + 5;
            scrollViewer.Margin = new Thickness(0, scrollViewerMargin, 0, 0);

            if ((int)instance.Height <= titleBar.Height) _isMinimized = true;
            if (instance.Minimized)
            {
                _isMinimized = instance.Minimized;
                this.Height = titleBarHeight;
            }
            else
            {
                this.Height = instance.Height;
            }
            titleStackPanel.MouseEnter += (s, e) => AnimateSymbolIcon(frameTypeSymbol, Instance.TitleFontSize, 1, 5);
            titleStackPanel.MouseLeave += (s, e) => AnimateSymbolIcon(frameTypeSymbol, 0, 0, 0);

            _checkForChages = true;
            FileItems = new BulkObservableCollection<FileItem>();
            string appDataPath = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "DeskFrame"
            );

            if (instance.Folder.StartsWith(appDataPath, StringComparison.OrdinalIgnoreCase))
            {
                Instance.IsShortcutsOnly = true;
                Instance.ShowShortcutArrow = false;
            }
            if (instance.Folder == "empty")
            {
                showFolder.Visibility = Visibility.Hidden;
                addFolder.Visibility = Visibility.Visible;
            }
            else if (!instance.IsFolderMissing)
            {
                LoadingProgressRing.Visibility = Visibility.Visible;
                LoadFiles(instance.Folder);
                title.Text = Instance.TitleText == "" ? Instance.Name : Instance.TitleText;

                DataContext = this;
            }
            else if (instance.IsFolderMissing)
            {
                title.Text = Instance.TitleText == "" ? Instance.Name : Instance.TitleText;
                DataContext = this;
                missingFolderGrid.Visibility = Visibility.Visible;
            }
            InitializeFileWatchers();

            if (Instance.SnapWidthToIconWidth_PlusScrollbarWidth)
            {
                FileWrapPanel.Margin = new Thickness(6, 5, 0, 5);
            }
            else
            {
                FileWrapPanel.Margin = new Thickness(0, 0, 0, 0);
            }

            _collectionView = CollectionViewSource.GetDefaultView(FileItems);
            _originalHeight = Instance.Height;
            titleBar.Background = new SolidColorBrush((Color)System.Windows.Media.ColorConverter.ConvertFromString(Instance.TitleBarColor));
            title.Foreground = new SolidColorBrush((Color)System.Windows.Media.ColorConverter.ConvertFromString(Instance.TitleTextColor));
            titleBarIcons.Opacity = Instance.HideTitleBarIconsWhenInactive ? 0 : 1;

            if (Instance.TitleFontFamily != null)
            {
                try
                {
                    title.FontFamily = new System.Windows.Media.FontFamily(Instance.TitleFontFamily);
                }
                catch
                {
                }
            }
            if (Instance.ItemFontFamily != null)
            {
                try
                {
                    this.Resources["ItemFont"] = new System.Windows.Media.FontFamily(Instance.ItemFontFamily);
                }
                catch
                {
                }
            }
            if (Instance.ShowInGrid)
            {
                showFolder.Visibility = Visibility.Visible;
                showFolderInGrid.Visibility = Visibility.Hidden;
            }
            else
            {
                showFolder.Visibility = Visibility.Hidden;
                showFolderInGrid.Visibility = Visibility.Visible;
            }
            ChangeBackgroundOpacity(Instance.Opacity);
        }
        private void Window_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            if (e.ClickCount == 2)
            {
                if (e.GetPosition(this).Y <= titleBar.Height)
                {
                    Minimize_MouseLeftButtonDown(null, null);
                    return;
                }
            }
            else if (e.ButtonState == MouseButtonState.Pressed)
            {
                KeepWindowBehind();
                if (!_isLocked)
                {
                    _dragMovingWinddow = true;
                    this.DragMove();
                }
                return;
            }
        }
        private void Window_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            _dragMovingWinddow = false;
        }
        private void AnimateSymbolIcon(UIElement target, double widthTo, double opacityTo, double marginTo)
        {
            var marginAnimation = new ThicknessAnimation
            {
                To = new Thickness(0, 0, marginTo, 0),
                Duration = TimeSpan.FromSeconds(0.1),
                EasingFunction = new CubicEase { EasingMode = EasingMode.EaseInOut }
            };
            var widthAnimation = new DoubleAnimation
            {
                To = widthTo,
                Duration = TimeSpan.FromSeconds(0.1),
                EasingFunction = new CubicEase { EasingMode = EasingMode.EaseInOut }
            };

            var opacityAnimation = new DoubleAnimation
            {
                To = opacityTo,
                Duration = TimeSpan.FromSeconds(0.1),
                EasingFunction = new CubicEase { EasingMode = EasingMode.EaseInOut }
            };

            target.BeginAnimation(FrameworkElement.MarginProperty, marginAnimation);
            target.BeginAnimation(FrameworkElement.WidthProperty, widthAnimation);
            target.BeginAnimation(UIElement.OpacityProperty, opacityAnimation);
        }

        private void AnimateChevron(bool flip, bool onLoad, double animationSpeed)
        {


            var rotateTransform = ChevronRotate;

            int angleToAnimateTo;
            int duration;
            if (onLoad)
            {
                angleToAnimateTo = flip ? 0 : 180;
                duration = 10;
            }
            else
            {
                angleToAnimateTo = (rotateTransform.Angle == 180) ? 0 : 180;
                duration = (int)(200 / animationSpeed);
            }
            if (_isLocked) duration = (int)(200 / animationSpeed);

            var rotateAnimation = new DoubleAnimation
            {
                From = rotateTransform.Angle,
                To = angleToAnimateTo,
                Duration = (animationSpeed == 0) ?
                    TimeSpan.FromMilliseconds(40) :
                    TimeSpan.FromMilliseconds(duration),
                EasingFunction = new QuadraticEase { EasingMode = EasingMode.EaseInOut }
            };

            _canAnimate = false;
            rotateAnimation.Completed += (s, e) => _canAnimate = true;

            rotateTransform.BeginAnimation(RotateTransform.AngleProperty, rotateAnimation);
        }

        private void Minimize_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {

            AnimateChevron(_isMinimized, false, Instance.AnimationSpeed);
            if (showFolder.Visibility == Visibility.Hidden && showFolderInGrid.Visibility == Visibility.Hidden)
            {
                return;
            }
            if (!_isMinimized)
            {
                _originalHeight = this.ActualHeight;
                _isMinimized = true;
                Instance.Minimized = true;
                // Debug.WriteLine("minimize: " + Instance.Height);
                AnimateWindowHeight(titleBar.Height, Instance.AnimationSpeed);
            }
            else
            {
                WindowBackground.CornerRadius = new CornerRadius(
                         topLeft: WindowBackground.CornerRadius.TopLeft,
                         topRight: WindowBackground.CornerRadius.TopRight,
                         bottomRight: 5.0,
                         bottomLeft: 5.0
                      );
                _isMinimized = false;
                Instance.Minimized = false;

                // Debug.WriteLine("unminimize: " + Instance.Height);
                AnimateWindowHeight(Instance.Height, Instance.AnimationSpeed);
            }
            HandleWindowMove(false);
        }

        private void ToggleFileExtension_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            ToggleFileExtension();
            LoadFiles(_currentFolderPath);
            UpdateFileExtensionIcon();
        }

        private void ToggleHiddenFiles_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            ToggleHiddenFiles();
            LoadFiles(_currentFolderPath);
            UpdateHiddenFilesIcon();
        }
        private void OpenFolder()
        {
            try
            {
                Process.Start(new ProcessStartInfo(_currentFolderPath) { UseShellExecute = true });
            }
            catch
            { }
        }
        private void UpdateFileExtensionIcon()
        {
            if (Instance.ShowFileExtension)
            {
                FileExtensionIcon.Symbol = SymbolRegular.DocumentSplitHint24;
            }
            else
            {
                FileExtensionIcon.Symbol = SymbolRegular.DocumentSplitHintOff24;
            }
        }

        private void UpdateHiddenFilesIcon()
        {
            if (Instance.ShowHiddenFiles)
            {
                HiddenFilesIcon.Symbol = SymbolRegular.Eye24;
            }
            else
            {
                HiddenFilesIcon.Symbol = SymbolRegular.EyeOff24;
            }
        }
        public void AnimateWindowOpacity(double value, double animationSpeed)
        {
            var animation = new DoubleAnimation
            {
                To = value,
                Duration = animationSpeed == 0 ?
                    TimeSpan.FromSeconds(0.1) :
                    TimeSpan.FromSeconds(0.2 / animationSpeed),
            };
            this.BeginAnimation(OpacityProperty, animation);
        }
        public void AnimateGrayScale(double oldValue, double newValue)
        {
            var animation = new DoubleAnimation
            {
                From = oldValue,
                To = newValue,
                Duration = TimeSpan.FromSeconds(0.1),
                FillBehavior = FillBehavior.HoldEnd
            };
            _grayscaleEffect.BeginAnimation(GrayscaleEffect.StrengthProperty, animation);
        }
        private void AnimateActiveColor(double animationSpeed)
        {
            if (Instance.ActiveBackgroundEnabled
                || Instance.ActiveBorderEnabled
                || Instance.ActiveTitleTextEnabled
                || Instance.GrayScaleEnabled && Instance.GrayScaleEnabled_InactiveOnly)
            {
                _mouseIsOver = IsCursorWithinWindowBounds();
            }
            if (Instance.GrayScaleEnabled && Instance.GrayScaleEnabled_InactiveOnly)
            {
                var animation = new DoubleAnimation
                {
                    From = _mouseIsOver ? Instance.MaxGrayScaleStrength : 0.0,
                    To = _mouseIsOver ? 0.0 : Instance.MaxGrayScaleStrength,
                    Duration = animationSpeed == 0 ? TimeSpan.FromSeconds(0)
                                                   : TimeSpan.FromSeconds(0.2 / animationSpeed),
                    FillBehavior = FillBehavior.HoldEnd
                };

                _grayscaleEffect.BeginAnimation(GrayscaleEffect.StrengthProperty, animation);
            }
            if (Instance.ActiveBorderEnabled)
            {
                if (!Instance.BorderEnabled)
                {
                    WindowBorder.BorderBrush = new SolidColorBrush((Color)ColorConverter.ConvertFromString("#00000000"));
                    WindowBorder.BorderThickness = new Thickness(1.3);
                }

                // rebind to unfreeze the brush so that the animation can be applied
                WindowBorder.SetBinding(Border.BorderBrushProperty, new Binding("Instance.BorderColor")
                {
                    Source = this,
                });

                var backgroundColorAnimation = new ColorAnimation
                {
                    From = _mouseIsOver ? !Instance.BorderEnabled
                                            ? (Color)ColorConverter.ConvertFromString("#00000000")
                                            : (Color)ColorConverter.ConvertFromString(Instance.BorderColor)
                                        : (Color)ColorConverter.ConvertFromString(Instance.ActiveBorderColor),

                    To = _mouseIsOver ? (Color)ColorConverter.ConvertFromString(Instance.ActiveBorderColor)
                                        : !Instance.BorderEnabled
                                            ? (Color)ColorConverter.ConvertFromString("#00000000")
                                            : (Color)ColorConverter.ConvertFromString(Instance.BorderColor),

                    Duration = animationSpeed == 0 ? TimeSpan.FromSeconds(0)
                                                   : TimeSpan.FromSeconds(0.2 / animationSpeed)
                };
                WindowBorder.BorderBrush.BeginAnimation(SolidColorBrush.ColorProperty, backgroundColorAnimation);
                backgroundColorAnimation.Completed += (sender, e) =>
                {

                    WindowBorder.SetBinding(Border.BorderThicknessProperty, new Binding("Instance.BorderEnabled")
                    {
                        Source = this,
                        Converter = (IValueConverter)Resources["BooleanToBorderThicknessConverter"]
                    });
                };
            }
            else
            {

                WindowBorder.SetBinding(Border.BorderThicknessProperty, new Binding("Instance.BorderEnabled")
                {
                    Source = this,
                    Converter = (IValueConverter)Resources["BooleanToBorderThicknessConverter"]
                });
            }

            if (Instance.ActiveBackgroundEnabled)
            {
                var borderColorAnimation = new ColorAnimation
                {
                    From = _mouseIsOver ? (Color)ColorConverter.ConvertFromString(Instance.ListViewBackgroundColor)
                                        : (Color)ColorConverter.ConvertFromString(Instance.ActiveBackgroundColor),
                    To = _mouseIsOver ? (Color)ColorConverter.ConvertFromString(Instance.ActiveBackgroundColor)
                                        : (Color)ColorConverter.ConvertFromString(Instance.ListViewBackgroundColor),
                    Duration = animationSpeed == 0 ? TimeSpan.FromSeconds(0)
                                                   : TimeSpan.FromSeconds(0.2 / animationSpeed)
                };
                WindowBackground.Background.BeginAnimation(SolidColorBrush.ColorProperty, borderColorAnimation);
            }
            if (Instance.ActiveTitleTextEnabled)
            {
                var titleBarItemsColorAnimation = new ColorAnimation
                {
                    From = _mouseIsOver ? (Color)ColorConverter.ConvertFromString(Instance.TitleTextColor)
                                       : (Color)ColorConverter.ConvertFromString(Instance.ActiveTitleTextColor),
                    To = _mouseIsOver ? (Color)ColorConverter.ConvertFromString(Instance.ActiveTitleTextColor)
                                       : (Color)ColorConverter.ConvertFromString(Instance.TitleTextColor),
                    Duration = animationSpeed == 0 ? TimeSpan.FromSeconds(0)
                                                  : TimeSpan.FromSeconds(0.2 / animationSpeed)
                };
                title.Foreground.BeginAnimation(SolidColorBrush.ColorProperty, titleBarItemsColorAnimation);
            }
        }

        private void AnimateWindowHeight(double targetHeight, double animationSpeed)
        {
            double currentHeight = this.ActualHeight;

            var freezeAnimation = new DoubleAnimation
            {
                To = currentHeight,
                Duration = TimeSpan.Zero,
                FillBehavior = FillBehavior.HoldEnd
            };
            this.BeginAnimation(HeightProperty, freezeAnimation);

            var animation = new DoubleAnimation
            {
                To = targetHeight,
                Duration = animationSpeed == 0 ?
                    TimeSpan.FromSeconds(0) :
                    TimeSpan.FromSeconds(0.2 / animationSpeed),
                EasingFunction = new QuadraticEase()
            };
            animation.Completed += (s, e) =>
            {
                _canAnimate = true;
                if (targetHeight == titleBar.Height)
                {
                    scrollViewer.ScrollToTop();
                }
                //WindowChrome.SetWindowChrome(this, Instance.IsLocked ?
                //new WindowChrome
                //{
                //    ResizeBorderThickness = new Thickness(0),
                //    CaptionHeight = 0
                //}
                //: _isOnBottom ?
                //    new WindowChrome
                //    {
                //        GlassFrameThickness = new Thickness(5),
                //        CaptionHeight = 0,
                //        ResizeBorderThickness = new Thickness(0, Instance.Minimized ? 0 : 5, 5, 0),
                //        CornerRadius = new CornerRadius(5)
                //    } :
                //    new WindowChrome
                //    {
                //        GlassFrameThickness = new Thickness(5),
                //        CaptionHeight = 0,
                //        ResizeBorderThickness = new Thickness(5, 0, 5, Instance.Minimized ? 0 : 5),
                //        CornerRadius = new CornerRadius(5)
                //    }
                // );
            };
            _canAnimate = false;
            this.BeginAnimation(HeightProperty, animation);
        }

        public void InitializeFileWatchers()
        {
            if (Instance.Folder != null && Instance.Folder != "empty")
            {
                if (_parentWatcher != null)
                {
                    _parentWatcher.Created -= OnParentChanged;
                    _parentWatcher.Deleted -= OnParentChanged;
                    _parentWatcher.Renamed -= OnParentRenamed;
                }
                _parentWatcher = new FileSystemWatcher(Path.GetDirectoryName(Instance.Folder))
                {
                    NotifyFilter = NotifyFilters.DirectoryName,
                    IncludeSubdirectories = false,
                    EnableRaisingEvents = true
                };
                _parentWatcher.Created += OnParentChanged;
                _parentWatcher.Deleted += OnParentChanged;
                _parentWatcher.Renamed += OnParentRenamed;
            }

            if (!Path.Exists(Instance.Folder) && Instance.Folder != "empty")
            {
                missingFolderGrid.Visibility = Visibility.Visible;
                return;
            }
            else
            {
                missingFolderGrid.Visibility = Visibility.Hidden;
            }
            if (Instance.Folder != "empty")
            {
                if (_fileWatcher != null)
                {
                    _fileWatcher.Created -= OnFileChanged;
                    _fileWatcher.Deleted -= OnFileChanged;
                    _fileWatcher.Renamed -= OnFileRenamed;
                    _fileWatcher.Changed -= OnFileChanged;
                }
                _fileWatcher = new FileSystemWatcher(_currentFolderPath)
                {
                    NotifyFilter = NotifyFilters.FileName | NotifyFilters.DirectoryName | NotifyFilters.LastWrite,
                    IncludeSubdirectories = false,
                    EnableRaisingEvents = true
                };
                _fileWatcher.Created += OnFileChanged;
                _fileWatcher.Deleted += OnFileChanged;
                _fileWatcher.Renamed += OnFileRenamed;
                _fileWatcher.Changed += OnFileChanged;
            }
        }
        private void OnParentRenamed(object sender, RenamedEventArgs e)
        {
            if (e.Name!.Equals(Path.GetFileName(Instance.Folder), StringComparison.OrdinalIgnoreCase))
            {
                Dispatcher.Invoke(() =>
                {
                    if (!Path.Exists(Instance.Folder) && Instance.Folder != "empty")
                    {
                        PathToBackButton.Visibility = Visibility.Collapsed;
                        missingFolderGrid.Visibility = Visibility.Visible;
                        FileItems.Clear();
                    }
                    else
                    {
                        missingFolderGrid.Visibility = Visibility.Hidden;
                        LoadFiles(Instance.Folder);
                        InitializeFileWatchers();
                    }
                });
            }
            if (e.OldName!.Equals(Path.GetFileName(Instance.Folder), StringComparison.OrdinalIgnoreCase))
            {

                var lastInstanceName = Instance.Name;
                Dispatcher.Invoke(() =>
                {
                    Instance.Folder = e.FullPath;
                    Instance.IsFolderMissing = false;
                    _currentFolderPath = Instance.Folder;
                    Instance.Name = Path.GetFileName(e.Name!);
                    MainWindow._controller.WriteOverInstanceToKey(Instance, lastInstanceName);
                    title.Text = Instance.TitleText == "" ? Instance.Name : Instance.TitleText;
                    PathToBackButton.Visibility = Visibility.Collapsed;
                    missingFolderGrid.Visibility = Visibility.Hidden;
                    foreach (var item in FileItems)
                    {
                        item.FullPath = item.FullPath!.Replace(@$"\{e.OldName}\", @$"\{e.Name}\");
                    }
                    InitializeFileWatchers();

                });
            }
        }
        private void OnParentChanged(object sender, FileSystemEventArgs e)
        {

            if (e.Name.Equals(Path.GetFileName(Instance.Folder), StringComparison.OrdinalIgnoreCase))
            {
                Dispatcher.Invoke(() =>
                {
                    if (!Path.Exists(Instance.Folder) && Instance.Folder != "empty")
                    {
                        PathToBackButton.Visibility = Visibility.Collapsed;
                        missingFolderGrid.Visibility = Visibility.Visible;
                        FileItems.Clear();
                    }
                    else
                    {
                        missingFolderGrid.Visibility = Visibility.Hidden;
                        LoadFiles(Instance.Folder);
                        InitializeFileWatchers();
                    }
                });
            }
        }
        private void OnFileChanged(object sender, FileSystemEventArgs e)
        {
            Dispatcher.Invoke(() =>
            {
                if ((!Path.Exists(Instance.Folder) && Instance.Folder != "empty") || e.Name == Instance.Folder)
                {
                    PathToBackButton.Visibility = Visibility.Collapsed;
                    missingFolderGrid.Visibility = Visibility.Visible;
                    return;
                }
                else
                {
                    missingFolderGrid.Visibility = Visibility.Hidden;
                }
                Debug.WriteLine($"File changed: {e.ChangeType} - {e.FullPath}");

                if (_debounceTimer == null)
                {
                    _debounceTimer = new DispatcherTimer
                    {
                        Interval = TimeSpan.FromMilliseconds(250)
                    };
                    _debounceTimer.Tick += (s, args) =>
                    {
                        _debounceTimer.Stop();
                        LoadFiles(_currentFolderPath);
                    };
                }
                else
                {
                    _debounceTimer.Stop();
                }
                _debounceTimer.Start();
            });
        }
        private void OnFileRenamed(object sender, RenamedEventArgs e)
        {
            Dispatcher.Invoke(() =>
            {
                Debug.WriteLine($"File renamed: {e.OldFullPath} to {e.FullPath}");
                var renamedItem = FileItems.FirstOrDefault(item => item.FullPath == e.OldFullPath);

                if (renamedItem != null)
                {
                    renamedItem.FullPath = e.FullPath;

                    string fileName = Path.GetFileName(e.FullPath);
                    Debug.WriteLine("FILENAME: " + fileName);
                    if (!renamedItem.IsFolder)
                    {
                        Debug.WriteLine("NOT FOLDER");
                        string actualExt = Path.GetExtension(fileName);
                        renamedItem.Name = Instance.ShowFileExtension || string.IsNullOrEmpty(actualExt)
                             ? fileName
                             : fileName.Substring(0, fileName.Length - actualExt.Length);
                    }
                    else
                    {
                        Debug.WriteLine("FOLDER");
                        renamedItem.Name = fileName;
                    }
                }

                SortItems();
            });
        }


        private void KeepWindowBehind()
        {
            if (_isTopmost)
            {
                return;
            }
            IntPtr HWND_BOTTOM = new IntPtr(1);
            var hwnd = new System.Windows.Interop.WindowInteropHelper(this).Handle;
            Interop.SetWindowPos(hwnd, HWND_BOTTOM, 0, 0, 0, 0, Interop.SWP_NOREDRAW | Interop.SWP_NOACTIVATE | Interop.SWP_NOMOVE | Interop.SWP_NOSIZE);
        }
        //public void KeepWindowBehind()
        //{
        //    bool keepOnBottom = this._keepOnBottom;
        //    this._keepOnBottom = false;
        //    Interop.SetWindowPos(new WindowInteropHelper(this).Handle, 1, 0, 0, 0, 0, 19U);
        //    this._keepOnBottom = keepOnBottom;
        //}

        private void ToggleHiddenFiles() => Instance.ShowHiddenFiles = !Instance.ShowHiddenFiles;
        private void ToggleIsLocked()
        {
            Instance.IsLocked = !Instance.IsLocked;
            var interopHelper = new WindowInteropHelper(this);
            interopHelper.EnsureHandle();
            IntPtr hwnd = interopHelper.Handle;
            SetParent(hwnd, IntPtr.Zero);
            WindowChrome.SetWindowChrome(this, Instance.IsLocked ?
                new WindowChrome
                {
                    ResizeBorderThickness = new Thickness(0),
                    CaptionHeight = 0,
                    CornerRadius = new CornerRadius(0)
                } :
                new WindowChrome
                {
                    GlassFrameThickness = new Thickness(0),
                    CaptionHeight = 0,
                    ResizeBorderThickness = new Thickness(5),
                    CornerRadius = new CornerRadius(0)
                }
            );
            SetAsDesktopChild();
            HandleWindowMove(true);

            this.Width += 1;
            this.Width -= 1;
        }
        private void ToggleFileExtension() => Instance.ShowFileExtension = !Instance.ShowFileExtension;

        public async void LoadFiles(string path)
        {
            loadFilesCancellationToken.Cancel();
            loadFilesCancellationToken.Dispose();
            loadFilesCancellationToken = new CancellationTokenSource();
            CancellationToken loadFiles_cts = loadFilesCancellationToken.Token;
            try
            {
                if (!Directory.Exists(path))
                {
                    return;
                }
                LoadingProgressRingFade(true);

                var fileEntries = await Task.Run(() =>
                {
                    if (loadFiles_cts.IsCancellationRequested)
                    {
                        LoadingProgressRingFade(false);
                        return new List<FileSystemInfo>();
                    }
                    var dirInfo = new DirectoryInfo(path);
                    var files = dirInfo.GetFiles();
                    var directories = dirInfo.GetDirectories();
                    _folderCount = directories.Count();
                    _fileCount = dirInfo.GetFiles().Count().ToString();
                    _folderSize = !Instance.CheckFolderSize ? "" : Task.Run(() => BytesToStringAsync(dirInfo.EnumerateFiles("*", SearchOption.AllDirectories).Sum(file => file.Length))).Result; var filteredFiles = files.Cast<FileSystemInfo>()
                                .Concat(directories)
                                .OrderBy(entry => entry.Name, StringComparer.OrdinalIgnoreCase)
                                .ToList();
                    if (!Instance.ShowHiddenFiles)
                        filteredFiles = filteredFiles.Where(entry => !entry.Attributes.HasFlag(FileAttributes.Hidden)).ToList();
                    if (Instance.FileFilterRegex != null)
                    {
                        var regex = new Regex(Instance.FileFilterRegex);
                        filteredFiles = filteredFiles.Where(entry => regex.IsMatch(entry.Name)).ToList();
                    }
                    return filteredFiles;
                }, loadFiles_cts);

                if (loadFiles_cts.IsCancellationRequested)
                {
                    LoadingProgressRingFade(false);
                    return;
                }
                if (Instance.LastAccesedToFirstRow)
                {
                    var wrapPanel = FindParentOrChild<WrapPanel>(FileWrapPanel);
                    if (wrapPanel != null)
                    {
                        double itemWidth = wrapPanel.ItemWidth;
                        ItemPerRow = (int)((this.Width) / itemWidth);
                    }
                    _previousItemPerRow = ItemPerRow;
                }
                fileEntries = await SortFileItemsToList(fileEntries, (int)Instance.SortBy, Instance.FolderOrder);

                if (Instance.EnableCustomItemsOrder)
                {
                    SortCustomOrder(fileEntries, Instance.CustomOrderFiles);
                }
                if (Instance.LastAccesedToFirstRow)
                {
                    FirstRowByLastAccessed(fileEntries, Instance.LastAccessedFiles, ItemPerRow);
                }
                var fileNames = new HashSet<string>(fileEntries.Select(f => f.Name));


                await Dispatcher.InvokeAsync(async () =>
                {
                    if (loadFiles_cts.IsCancellationRequested)
                    {
                        LoadingProgressRingFade(false);
                        return;
                    }
                    FileItems.BeginUpdate();
                    try
                    {
                        for (int i = FileItems.Count - 1; i >= 0; i--)  // Remove item that no longer exist
                        {
                            if (loadFiles_cts.IsCancellationRequested)
                            {
                                LoadingProgressRingFade(false);
                                return;
                            }
                            if (!fileNames.Contains(Path.GetFileName(FileItems[i].FullPath!)))
                            {
                                FileItems.RemoveAt(i);
                            }
                        }

                        foreach (var entry in fileEntries)
                        {
                            if (loadFiles_cts.IsCancellationRequested)
                            {
                                LoadingProgressRingFade(false);
                                return;
                            }

                            var existingItem = FileItems.FirstOrDefault(item => item.FullPath == entry.FullName);

                            long size = 0;
                            if (entry is FileInfo fileInfo)
                                size = fileInfo.Length;
                            else if (entry is DirectoryInfo directoryInfo && Instance.CheckFolderSize)
                                size = await Task.Run(() => GetDirectorySize(directoryInfo, loadFiles_cts));
                            size = size > int.MaxValue ? int.MaxValue : size;

                            string displaySize = entry is FileInfo ? await BytesToStringAsync(size)
                                                                   : Instance.CheckFolderSize ? await BytesToStringAsync(size)
                                                                                              : "";
                            var thumbnail = await GetThumbnailAsync(entry.FullName);
                            bool isFile = entry is FileInfo;
                            string actualExt = isFile ? Path.GetExtension(entry.Name) : string.Empty;
                            if (existingItem == null)
                            {
                                if (!string.IsNullOrEmpty(Instance.FileFilterHideRegex) &&
                                    new Regex(Instance.FileFilterHideRegex).IsMatch(entry.Name))
                                {
                                    continue;
                                }

                                FileItems.Add(new FileItem
                                {
                                    Name = Instance.ShowFileExtension || string.IsNullOrEmpty(actualExt)
                                        ? entry.Name
                                        : entry.Name.Substring(0, entry.Name.Length - actualExt.Length),
                                    FullPath = entry.FullName,
                                    IsFolder = !isFile,
                                    DateModified = entry.LastWriteTime,
                                    DateCreated = entry.CreationTime,
                                    FileType = isFile ? actualExt : string.Empty,
                                    ItemSize = (int)size,
                                    DisplaySize = displaySize,
                                    Thumbnail = thumbnail
                                });
                            }
                            else
                            {
                                existingItem.Name = Instance.ShowFileExtension || string.IsNullOrEmpty(actualExt)
                                        ? entry.Name
                                        : entry.Name.Substring(0, entry.Name.Length - actualExt.Length);
                                existingItem.FullPath = entry.FullName;
                                existingItem.IsFolder = string.IsNullOrEmpty(Path.GetExtension(entry.FullName));
                                existingItem.DateModified = entry.LastWriteTime;
                                existingItem.DateCreated = entry.CreationTime;
                                existingItem.FileType = entry is FileInfo ? entry.Extension : string.Empty;
                                existingItem.ItemSize = (int)size;
                                existingItem.DisplaySize = displaySize;
                                existingItem.Thumbnail = thumbnail;
                            }
                        }
                        var sortedList = FileItems.ToList();

                        FileItems.Clear();
                        foreach (var fileItem in sortedList)
                        {
                            if (Instance.FileFilterHideRegex != null && Instance.FileFilterHideRegex != ""
                              && new Regex(Instance.FileFilterHideRegex).IsMatch(fileItem.Name))
                            {
                                continue;
                            }
                            FileItems.Add(fileItem);
                        }
                        if (Instance.EnableCustomItemsOrder)
                        {
                            SortCustomOrderOc(FileItems, Instance.CustomOrderFiles);
                        }
                        if (Instance.LastAccesedToFirstRow)
                        {
                            FirstRowByLastAccessed(FileItems, Instance.LastAccessedFiles, ItemPerRow);
                        }
                    }
                    finally
                    {
                        FileItems.EndUpdate();
                    }
                    _lastUpdated = DateTime.Now;
                    int hiddenCount = Int32.Parse(_fileCount) - (FileItems.Count - _folderCount);
                    if (hiddenCount > 0)
                    {
                        _fileCount += $" ({hiddenCount} hidden)";
                    }
                    SortItems();
                    await Task.Run(async () =>
                    {
                        await Task.Delay(200);
                        Dispatcher.Invoke(() =>
                        {
                            LoadingProgressRingFade(false);
                        });
                    });
                    Debug.WriteLine("LOADEDDDDDDDD");
                });
            }
            catch (OperationCanceledException)
            {
                LoadingProgressRingFade(false);
                Debug.WriteLine("LoadFiles was canceled.");
            }
        }
        private void LoadingProgressRingFade(bool showLoading)
        {
            Storyboard fadeOut = (Storyboard)this.Resources["FadeOutLoadingProgressRingStoryboard"];
            Storyboard fadeIn = (Storyboard)this.Resources["FadeInLoadingProgressRingStoryboard"];

            if (showLoading)
            {
                LoadingProgressRing.IsIndeterminate = true;
                fadeIn.Begin();
            }
            else
            {
                try
                {
                    fadeOut.Completed += (s, e) =>
                    {
                        fadeOut.Completed -= (s, e) => { }; // cleanup
                        LoadingProgressRing.IsIndeterminate = false;
                    };
                }
                catch { }

                fadeOut.Begin();
            }
        }

        public void TitleBarIconsFadeAnimation(bool show)
        {
            Storyboard fadeIn = (Storyboard)this.Resources["FadeIn_titleBarIcons_Storyboard"];
            Storyboard fadeOut = (Storyboard)this.Resources["FadeOut_titleBarIcons_Storyboard"];

            if (show)
            {
                fadeIn.Begin();
            }
            else
            {
                fadeOut.Completed += (s, e) =>
                {
                    fadeOut.Completed -= (s, e) => { }; // cleanup
                };
                fadeOut.Begin();
            }
        }
        public void SortItems()
        {
            var sortedList = SortFileItems(FileItems, (int)Instance.SortBy, Instance.FolderOrder);

            if (Instance.EnableCustomItemsOrder)
            {
                SortCustomOrderOc(sortedList, Instance.CustomOrderFiles);
            }
            if (Instance.LastAccesedToFirstRow)
            {
                FirstRowByLastAccessed(sortedList, Instance.LastAccessedFiles, ItemPerRow);
            }
            FileItems.Clear();
            foreach (var fileItem in sortedList)
            {
                FileItems.Add(fileItem);
            }
        }
        private void FileListView_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            this.Focus();
            _canAutoClose = false;
            if (sender is not ListView listView)
                return;
            var point = e.GetPosition(listView);
            var element = listView.InputHitTest(point) as DependencyObject;
            while (element != null && element is not ListViewItem)
            {
                element = VisualTreeHelper.GetParent(element);
            }
            if (element is ListViewItem item && item.DataContext is FileItem clickedItem)
            {
                if (e.LeftButton == MouseButtonState.Pressed && e.ClickCount != 2)
                {
                    DataObject data = new DataObject(DataFormats.FileDrop, new string[] { clickedItem.FullPath! });
                    Task.Run(() =>
                    {
                        Thread.Sleep(5);
                        Application.Current.Dispatcher.Invoke(() =>
                        {
                            DragDrop.DoDragDrop(listView, data, DragDropEffects.Copy | DragDropEffects.Move);
                        });
                    });
                }
            }
        }
        private void FileListView_DoubleClick(object sender, MouseButtonEventArgs e)
        {
            if (sender is not ListView listView)
                return;
            var point = e.GetPosition(listView);
            var element = listView.InputHitTest(point) as DependencyObject;
            while (element != null && element is not ListViewItem)
            {
                element = VisualTreeHelper.GetParent(element);
            }
            if (element is ListViewItem item && item.DataContext is FileItem clickedItem)
            {
                try
                {
                    Process.Start(new ProcessStartInfo(clickedItem.FullPath!) { UseShellExecute = true });
                }
                catch
                {
                }
            }
        }
        private void FileListView_MouseRightButtonUp(object sender, MouseButtonEventArgs e)
        {
            _canAutoClose = false;
            if (sender is not ListView listView)
                return;
            var point = e.GetPosition(listView);
            var element = listView.InputHitTest(point) as DependencyObject;
            while (element != null && element is not ListViewItem)
            {
                element = VisualTreeHelper.GetParent(element);
            }
            if (element is ListViewItem item && item.DataContext is FileItem clickedFileItem)
            {
                var windowHelper = new WindowInteropHelper(this);
                FileInfo[] files = new FileInfo[1];
                files[0] = new FileInfo(clickedFileItem.FullPath!);
                Point cursorPosition = System.Windows.Forms.Cursor.Position;
                System.Windows.Point wpfPoint = new System.Windows.Point(cursorPosition.X, cursorPosition.Y);
                Point drawingPoint = new Point((int)wpfPoint.X, (int)wpfPoint.Y);
                _contextMenuIsOpen = true;
                scm.ContextMenuClosed += () =>
                {
                    _contextMenuIsOpen = false;
                };
                scm.ShowContextMenu(windowHelper.Handle, files, drawingPoint, (clickedFileItem.FullPath! == _currentFolderPath));
            }
        }
        private void MoveItemToPosition()
        {
            if (_itemUnderCursor == null || _draggedItem == null)
            {
                return;
            }
            _canChangeItemPosition = false;
            if (_draggedItem != _itemUnderCursor)
            {
                try
                {
                    int fromIndex = FileItems.IndexOf(_draggedItem);
                    int toIndex = FileItems.IndexOf(_itemUnderCursor);
                    FileItems.Move(fromIndex, toIndex);
                    _itemUnderCursor.IsMoveBarVisible = false;
                    _draggedItem.IsSelected = false;
                    _itemUnderCursor.Background = Brushes.Transparent;
                    AddToCustomOrder(_draggedItem.FullPath!, toIndex);
                }
                catch
                {
                    Debug.WriteLine("Failed to swap items");
                }
            }
        }
        private void AddToCustomOrder(string path, int index)
        {
            var fileId = GetFileId(path).ToString();
            var newList = new List<Tuple<string, string>>(Instance.CustomOrderFiles);
            newList.RemoveAll(t => t.Item1 == fileId);
            newList.Add(new Tuple<string, string>(fileId, index.ToString()));
            Instance.CustomOrderFiles = newList;
        }

        private static void DropLog(string msg)
        {
            try
            {
                string logDir = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "DeskFrame");
                if (!Directory.Exists(logDir)) Directory.CreateDirectory(logDir);
                string logFile = Path.Combine(logDir, "dragdrop_debug.log");
                File.AppendAllText(logFile, $"[{DateTime.Now:HH:mm:ss.fff}] {msg}{Environment.NewLine}");
            }
            catch { }
        }

        private void Window_Drop(object sender, DragEventArgs e)
        {
            _dragdropIntoFolder = false;
            _canAutoClose = false;
            Task.Run(async () =>
            {
                Thread.Sleep(300);
                _canAutoClose = true;
            });

            // === DIAGNOSTIC LOGGING ===
            try
            {
                DropLog("========== WINDOW_DROP FIRED ==========");
                var allFormats = e.Data.GetFormats();
                DropLog($"Available formats ({allFormats?.Length ?? 0}): {string.Join(", ", allFormats ?? Array.Empty<string>())}");
                foreach (var fmt in allFormats ?? Array.Empty<string>())
                {
                    try
                    {
                        bool present = e.Data.GetDataPresent(fmt);
                        DropLog($"  Format '{fmt}': present={present}");
                        if (present)
                        {
                            var fmtData = e.Data.GetData(fmt);
                            DropLog($"    DataType: {fmtData?.GetType()?.FullName ?? "null"}");
                            if (fmtData is string s) DropLog($"    Value: {s}");
                            else if (fmtData is string[] sa) DropLog($"    Values: {string.Join("; ", sa)}");
                            else if (fmtData is System.IO.MemoryStream ms2) DropLog($"    MemoryStream length: {ms2.Length}");
                        }
                    }
                    catch (Exception fmtEx) { DropLog($"  Format '{fmt}': ERROR {fmtEx.Message}"); }
                }
            }
            catch (Exception logEx) { DropLog($"Logging error: {logEx.Message}"); }

            // --- SYSTEM VIRTUAL SHELL ICONS DROP HANDLING (This PC, Recycle Bin, Control Panel, Network) ---
            bool virtualItemsHandled = false;
            try
            {
                DropLog("--- Calling GetVirtualShellItems ---");
                var virtualItems = GetVirtualShellItems(e.Data);
                DropLog($"GetVirtualShellItems returned {virtualItems?.Count ?? 0} items");
                if (virtualItems != null && virtualItems.Count > 0)
                {
                    virtualItemsHandled = true;
                    string targetFolder = !string.IsNullOrEmpty(_currentFolderPath) && _currentFolderPath != "empty" ? _currentFolderPath : Instance.Folder;
                    DropLog($"Target folder before init: '{targetFolder}'");
                    if (string.IsNullOrEmpty(targetFolder) || targetFolder == "empty")
                    {
                        targetFolder = Path.Combine(
                            Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData),
                            "DeskFrame",
                            Guid.NewGuid().ToString()
                        );
                        _currentFolderPath = targetFolder;
                        Directory.CreateDirectory(targetFolder);
                        Instance.Folder = targetFolder;
                        Instance.IsShortcutsOnly = true;
                        Instance.ShowShortcutArrow = false;
                        title.Text = "File frame";
                        Instance.TitleText = "File frame";
                        Instance.Name = Path.GetFileName(Instance.Folder);
                        MainWindow._controller.WriteInstanceToKey(Instance);
                        DataContext = this;
                        InitializeFileWatchers();
                        showFolder.Visibility = Visibility.Visible;
                        LoadingProgressRing.Visibility = Visibility.Visible;
                        addFolder.Visibility = Visibility.Hidden;
                        DropLog($"Initialized new folder: '{targetFolder}'");
                    }

                    foreach (var vItem in virtualItems)
                    {
                        DropLog($"  VItem: Display='{vItem.DisplayName}', Parsing='{vItem.ParsingPath}', IsFS={vItem.IsFileSystem}, FSPath='{vItem.FileSystemPath}', Icon='{vItem.IconLocation}'");
                        // Process ALL virtual items (both filesystem and non-filesystem)
                        if (!string.IsNullOrEmpty(vItem.ParsingPath) || !string.IsNullOrEmpty(vItem.FileSystemPath))
                        {
                            string cleanName = string.IsNullOrWhiteSpace(vItem.DisplayName) ? "System Icon" : vItem.DisplayName;
                            foreach (char c in Path.GetInvalidFileNameChars())
                            {
                                cleanName = cleanName.Replace(c, '_');
                            }

                            string shortcutPath = Path.Combine(targetFolder, $"{cleanName}.lnk");
                            int counter = 1;
                            while (File.Exists(shortcutPath))
                            {
                                shortcutPath = Path.Combine(targetFolder, $"{cleanName} ({counter++}).lnk");
                            }

                            WshShell shell = new WshShell();
                            IWshShortcut shortcut = (IWshShortcut)shell.CreateShortcut(shortcutPath);

                            if (vItem.IsFileSystem && !string.IsNullOrEmpty(vItem.FileSystemPath))
                            {
                                // Filesystem item (e.g. user profile folder) - point directly
                                shortcut.TargetPath = vItem.FileSystemPath;
                                DropLog($"  Creating FS shortcut -> '{vItem.FileSystemPath}'");
                            }
                            else
                            {
                                // Virtual shell item - use explorer.exe shell:::{CLSID}
                                shortcut.TargetPath = @"C:\Windows\explorer.exe";
                                shortcut.Arguments = vItem.ParsingPath;
                                DropLog($"  Creating virtual shortcut -> explorer.exe {vItem.ParsingPath}");
                            }

                            if (!string.IsNullOrEmpty(vItem.IconLocation))
                            {
                                shortcut.IconLocation = vItem.IconLocation;
                            }
                            else
                            {
                                shortcut.IconLocation = @"C:\Windows\System32\shell32.dll,0";
                            }
                            shortcut.Save();
                            DropLog($"  Shortcut saved: '{shortcutPath}' exists={File.Exists(shortcutPath)}");
                        }
                    }
                    LoadFiles(_currentFolderPath);
                    DropLog("Virtual items processed and LoadFiles called");
                }
            }
            catch (Exception ex)
            {
                DropLog($"ERROR in virtual shell item handling: {ex}");
                Debug.WriteLine("Error handling virtual shell item drop: " + ex.Message);
            }

            if (virtualItemsHandled && !e.Data.GetDataPresent(DataFormats.FileDrop))
            {
                return;
            }

            if (e.Data.GetDataPresent(DataFormats.FileDrop))
            {
                if (_canChangeItemPosition)
                {
                    MoveItemToPosition();
                    return;
                }

                // Ensure target folder exists before processing dropped items
                if (string.IsNullOrEmpty(_currentFolderPath) || _currentFolderPath == "empty" || !Directory.Exists(_currentFolderPath))
                {
                    Instance.Folder = Path.Combine(
                        Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData),
                        "DeskFrame",
                        Guid.NewGuid().ToString()
                    );
                    _currentFolderPath = Instance.Folder;
                    Directory.CreateDirectory(Instance.Folder);
                    Instance.IsShortcutsOnly = true;
                    Instance.ShowShortcutArrow = false;
                    title.Text = "File frame";
                    Instance.TitleText = "File frame";
                    Instance.Name = Path.GetFileName(Instance.Folder);
                    MainWindow._controller.WriteInstanceToKey(Instance);
                    DataContext = this;
                    InitializeFileWatchers();
                    showFolder.Visibility = Visibility.Visible;
                    LoadingProgressRing.Visibility = Visibility.Visible;
                    addFolder.Visibility = Visibility.Hidden;
                }

                string[] files = (string[])e.Data.GetData(DataFormats.FileDrop);
                foreach (var file in files)
                {
                    try
                    {
                        // Self-drop guard: skip files already in the current folder (from clicking icons inside frame)
                        string fileDir = Path.GetDirectoryName(file) ?? string.Empty;
                        if (!string.IsNullOrEmpty(_currentFolderPath) &&
                            string.Equals(fileDir, _currentFolderPath, StringComparison.OrdinalIgnoreCase))
                        {
                            DropLog($"Self-drop skipped: '{file}' already in current folder");
                            continue;
                        }

                        string ext = Path.GetExtension(file).ToLower();
                        bool isShortcutFile = ext == ".lnk" || ext == ".url";

                        if (Directory.Exists(file))
                        {
                            Debug.WriteLine("Folder detected: " + file);
                            if (!Instance.IsShortcutsOnly)
                            {
                                string destinationPath = Path.Combine(_currentFolderPath, Path.GetFileName(file));
                                Directory.Move(file, destinationPath);
                            }
                            else
                            {
                                CreateShortcut(file, _currentFolderPath);
                            }
                        }
                        else
                        {
                            Debug.WriteLine("File detected: " + file);
                            if (Instance.IsShortcutsOnly || isShortcutFile)
                            {
                                CreateShortcut(file, _currentFolderPath);
                            }
                            else
                            {
                                string destinationPath = Path.Combine(_currentFolderPath, Path.GetFileName(file));
                                try
                                {
                                    File.Copy(file, destinationPath, true);
                                }
                                catch
                                {
                                    File.Move(file, destinationPath);
                                }
                            }
                        }
                    }
                    catch (Exception ex)
                    {
                        Debug.WriteLine("Error processing dropped file: " + ex.Message);
                    }
                }

                LoadFiles(_currentFolderPath);
            }
        }


        private static bool GetShortcutDetails(string shortcutPath, out string targetPath, out string arguments, out string workingDirectory)
        {
            targetPath = string.Empty;
            arguments = string.Empty;
            workingDirectory = string.Empty;

            if (string.IsNullOrEmpty(shortcutPath) || !File.Exists(shortcutPath)) return false;
            if (!Path.GetExtension(shortcutPath).Equals(".lnk", StringComparison.OrdinalIgnoreCase)) return false;

            try
            {
                WshShell shell = new WshShell();
                IWshShortcut shortcut = (IWshShortcut)shell.CreateShortcut(shortcutPath);
                targetPath = shortcut.TargetPath?.Trim() ?? string.Empty;
                arguments = shortcut.Arguments?.Trim() ?? string.Empty;
                workingDirectory = shortcut.WorkingDirectory?.Trim() ?? string.Empty;
                return true;
            }
            catch
            {
                return false;
            }
        }

        private static string ExtractProfileOrDifferentiatorName(string arguments, string workingDirectory)
        {
            if (!string.IsNullOrWhiteSpace(arguments))
            {
                var match = System.Text.RegularExpressions.Regex.Match(arguments, @"--profile-directory=[""]?([^""\s]+)[""]?", System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (match.Success)
                {
                    string profile = match.Groups[1].Value.Trim();
                    if (!string.IsNullOrEmpty(profile)) return profile;
                }

                match = System.Text.RegularExpressions.Regex.Match(arguments, @"--launch-product=([^\s]+)", System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (match.Success)
                {
                    string product = match.Groups[1].Value.Trim().Replace('_', ' ');
                    if (!string.IsNullOrEmpty(product))
                    {
                        return System.Globalization.CultureInfo.CurrentCulture.TextInfo.ToTitleCase(product);
                    }
                }

                match = System.Text.RegularExpressions.Regex.Match(arguments, @"--user-data-dir=[""]?([^""\r\n]+)[""]?", System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (match.Success)
                {
                    string userData = match.Groups[1].Value.Trim();
                    string folderName = Path.GetFileName(userData.TrimEnd('\\', '/'));
                    if (!string.IsNullOrEmpty(folderName)) return folderName;
                }

                match = System.Text.RegularExpressions.Regex.Match(arguments, @"(?:-profile|-p)\s+[""]?([^""\s]+)[""]?", System.Text.RegularExpressions.RegexOptions.IgnoreCase);
                if (match.Success)
                {
                    string pName = match.Groups[1].Value.Trim();
                    if (!string.IsNullOrEmpty(pName)) return pName;
                }
            }

            if (!string.IsNullOrWhiteSpace(workingDirectory))
            {
                try
                {
                    string folderName = Path.GetFileName(workingDirectory.TrimEnd('\\', '/'));
                    if (!string.IsNullOrEmpty(folderName)) return folderName;
                }
                catch { }
            }

            return null;
        }

        private static bool IsSystemShellPath(string path, out string clsid, out string friendlyName)
        {
            clsid = null;
            friendlyName = null;
            if (string.IsNullOrEmpty(path)) return false;

            string p = path.ToUpperInvariant();

            if (p.Contains("20D04FE0-3AEA-1069-A2D8-08002B30309D"))
            {
                clsid = "::{20D04FE0-3AEA-1069-A2D8-08002B30309D}";
                friendlyName = "This PC";
                return true;
            }
            if (p.Contains("645FF040-5081-101B-9F08-002B101979E5") || p.Contains("645FF040-5081-101B-9F08-00AA002F954E"))
            {
                clsid = "::{645FF040-5081-101B-9F08-00AA002F954E}";
                friendlyName = "Recycle Bin";
                return true;
            }
            if (p.Contains("26EE0668-A00A-44D7-9371-BEB064C98683") || p.Contains("21EC2020-3AEA-1069-A2DD-08002B30309D"))
            {
                clsid = "::{26EE0668-A00A-44D7-9371-BEB064C98683}";
                friendlyName = "Control Panel";
                return true;
            }
            if (p.Contains("F02C5576-C192-4B59-9B36-D55077973D44"))
            {
                clsid = "::{F02C5576-C192-4B59-9B36-D55077973D44}";
                friendlyName = "Network";
                return true;
            }
            if (p.Contains("59031A47-3F72-44A7-89C5-5595FE6B30EE"))
            {
                clsid = "::{59031A47-3F72-44A7-89C5-5595FE6B30EE}";
                friendlyName = "User Files";
                return true;
            }
            if (p.StartsWith("SHELL:::{") || p.StartsWith("::{"))
            {
                clsid = path;
                friendlyName = "System Icon";
                return true;
            }

            return false;
        }

        private static bool CreateSystemShortcutInFolder(string clsid, string friendlyName, string folder)
        {
            if (string.IsNullOrEmpty(folder)) return false;
            if (!Directory.Exists(folder)) Directory.CreateDirectory(folder);

            string cleanName = string.IsNullOrWhiteSpace(friendlyName) ? "System Icon" : friendlyName;
            foreach (char c in Path.GetInvalidFileNameChars())
            {
                cleanName = cleanName.Replace(c, '_');
            }

            string shortcutPath = Path.Combine(folder, $"{cleanName}.lnk");
            int counter = 1;
            while (File.Exists(shortcutPath))
            {
                shortcutPath = Path.Combine(folder, $"{cleanName} ({counter++}).lnk");
            }

            try
            {
                WshShell shell = new WshShell();
                IWshShortcut shortcut = (IWshShortcut)shell.CreateShortcut(shortcutPath);
                shortcut.TargetPath = @"C:\Windows\explorer.exe";

                if (!clsid.StartsWith("shell:::", StringComparison.OrdinalIgnoreCase))
                {
                    shortcut.Arguments = "shell:::" + clsid.TrimStart(':');
                }
                else
                {
                    shortcut.Arguments = clsid;
                }

                string iconLocation = GetDeskFrameSystemIconForParsingPath(clsid);
                if (!string.IsNullOrEmpty(iconLocation))
                {
                    shortcut.IconLocation = iconLocation;
                }
                else
                {
                    shortcut.IconLocation = @"C:\Windows\System32\shell32.dll,0";
                }
                shortcut.Save();
                return true;
            }
            catch (Exception ex)
            {
                Debug.WriteLine("Error creating system shortcut: " + ex.Message);
                return false;
            }
        }

        void CreateShortcut(string filePath, string shortcutFolder = null)
        {
            string folder = !string.IsNullOrEmpty(shortcutFolder) ? shortcutFolder : Path.GetDirectoryName(filePath);
            if (string.IsNullOrEmpty(folder)) return;

            // Check if filePath is a system shell CLSID or virtual path
            if (IsSystemShellPath(filePath, out string clsid, out string friendlyName))
            {
                CreateSystemShortcutInFolder(clsid, friendlyName, folder);
                return;
            }

            string ext = Path.GetExtension(filePath).ToLower();

            // Handle .url Web Shortcuts
            if (ext == ".url")
            {
                string destPath = Path.Combine(folder, Path.GetFileName(filePath));
                int counter = 1;
                while (File.Exists(destPath))
                {
                    string nameNoExt = Path.GetFileNameWithoutExtension(filePath);
                    destPath = Path.Combine(folder, $"{nameNoExt} ({counter++}).url");
                }
                File.Copy(filePath, destPath, true);
                return;
            }

            // Handle .lnk Shortcut Files
            if (ext == ".lnk")
            {
                GetShortcutDetails(filePath, out string dropTarget, out string dropArgs, out string dropWorkDir);

                // Check if .lnk target or arguments point to system shell CLSID
                if (IsSystemShellPath(dropTarget, out string subClsid, out string subName) || IsSystemShellPath(dropArgs, out subClsid, out subName))
                {
                    CreateSystemShortcutInFolder(subClsid, subName, folder);
                    return;
                }

                string baseName = Path.GetFileNameWithoutExtension(filePath);
                string destShortcutPath = Path.Combine(folder, baseName + ".lnk");
                int counter = 1;

                while (File.Exists(destShortcutPath))
                {
                    GetShortcutDetails(destShortcutPath, out string existingTarget, out string existingArgs, out string existingWorkDir);

                    bool isExactDuplicate = string.Equals(dropTarget, existingTarget, StringComparison.OrdinalIgnoreCase) &&
                                            string.Equals(dropArgs, existingArgs, StringComparison.OrdinalIgnoreCase) &&
                                            string.Equals(dropWorkDir, existingWorkDir, StringComparison.OrdinalIgnoreCase);

                    if (isExactDuplicate)
                    {
                        break;
                    }

                    string profileTag = ExtractProfileOrDifferentiatorName(dropArgs, dropWorkDir);
                    if (!string.IsNullOrEmpty(profileTag) && counter == 1)
                    {
                        destShortcutPath = Path.Combine(folder, $"{baseName} - {profileTag}.lnk");
                    }
                    else
                    {
                        destShortcutPath = Path.Combine(folder, $"{baseName} ({counter++}).lnk");
                    }
                }

                File.Copy(filePath, destShortcutPath, true);
                return;
            }

            // Handle Raw Files / Folders (Create new .lnk)
            string shortcutPath = Path.Combine(folder, Path.GetFileNameWithoutExtension(filePath) + ".lnk");
            int fileCounter = 1;
            while (File.Exists(shortcutPath))
            {
                string nameNoExt = Path.GetFileNameWithoutExtension(filePath);
                shortcutPath = Path.Combine(folder, $"{nameNoExt} ({fileCounter++}).lnk");
            }

            WshShell shell = new WshShell();
            IWshShortcut shortcut = (IWshShortcut)shell.CreateShortcut(shortcutPath);

            shortcut.TargetPath = filePath;
            shortcut.WorkingDirectory = Path.GetDirectoryName(filePath);
            try
            {
                shortcut.Description = Path.GetFileName(filePath);
            }
            catch
            {
            }
            shortcut.Save();
        }

        private void FileItem_LeftMouseButtonDown(object sender, MouseButtonEventArgs e)
        {
            this.Focus();
            var clickedFileItem = (sender as Border)?.DataContext as FileItem;

            if (clickedFileItem != null)
            {
                if (!(Keyboard.IsKeyDown(Key.LeftCtrl)
                || Keyboard.IsKeyDown(Key.RightCtrl)
                || Keyboard.IsKeyDown(Key.LeftShift)
                || Keyboard.IsKeyDown(Key.RightShift)))
                {
                    clickedFileItem.IsSelected = true;
                    if (!_contextMenuIsOpen)
                    {
                        _selectedItems.Clear();

                        foreach (var fileItem in FileItems)
                        {
                            if (fileItem != clickedFileItem)
                            {
                                fileItem.IsSelected = false;
                                fileItem.Background = Brushes.Transparent;
                            }
                        }
                    }
                }
                else
                {
                    clickedFileItem.IsSelected = !clickedFileItem.IsSelected;
                }
                if (clickedFileItem.IsSelected && !_selectedItems.Contains(clickedFileItem))
                {
                    _selectedItems.Add(clickedFileItem);
                }
            }
            if (e.ClickCount == 2 && sender is Border border && border.DataContext is FileItem clickedItem)
            {
                try
                {
                    if (Instance.FolderOpenInsideFrame && clickedItem.IsFolder)
                    {
                        _currentFolderPath = clickedItem.FullPath;
                        PathToBackButton.Visibility = _currentFolderPath == Instance.Folder
                            ? Visibility.Collapsed : Visibility.Visible;
                        Search.Margin = PathToBackButton.Visibility == Visibility.Visible ?
                                        new Thickness(PathToBackButton.Width + 4, 0, 0, 0) : new Thickness(0, 0, 0, 0);
                        InitializeFileWatchers();
                        FileItems.Clear();
                        LoadFiles(clickedItem.FullPath);
                    }
                    else
                    {
                        Process.Start(new ProcessStartInfo(clickedItem.FullPath!) { UseShellExecute = true });
                    }
                    if (Instance.LastAccesedToFirstRow)
                    {
                        var fileId = GetFileId(clickedFileItem.FullPath!).ToString();
                        var newList = new List<string>(Instance.LastAccessedFiles);
                        newList.Remove(fileId);
                        newList.Insert(0, fileId);
                        Instance.LastAccessedFiles = newList;
                        var wrapPanel = FindParentOrChild<WrapPanel>(FileWrapPanel);
                        if (wrapPanel != null)
                        {
                            double itemWidth = wrapPanel.ItemWidth;
                            ItemPerRow = (int)((this.Width) / itemWidth);
                        }
                        FirstRowByLastAccessed(FileItems, Instance.LastAccessedFiles, ItemPerRow);
                    }
                }
                catch //(Exception ex)
                {
                    //  MessageBox.Show($"Error opening file: {ex.Message}", "Error", MessageBoxButton.OK, MessageBoxImage.Error);
                }
            }
            else if (!(Keyboard.IsKeyDown(Key.LeftCtrl) || Keyboard.IsKeyDown(Key.RightCtrl)) && e.LeftButton == MouseButtonState.Pressed && sender is Border dragBorder)
            {
                if (dragBorder.DataContext is FileItem fileItem)
                {
                    if (((GetAsyncKeyState(0xA4) & 0x8000) != 0 || (GetAsyncKeyState(0xA5) & 0x8000) != 0))
                    {
                        _draggedItem = fileItem;
                    }

                    // Store drag start info — actual DoDragDrop is triggered in PreviewMouseMove after threshold
                    _pendingDragItem = fileItem;
                    _pendingDragBorder = dragBorder;
                    _dragStartPoint = e.GetPosition(this);
                }
            }
            if (clickedFileItem != null && (Keyboard.IsKeyDown(Key.LeftCtrl) || Keyboard.IsKeyDown(Key.RightCtrl)))
            {
                if (!_selectedItems.Contains(clickedFileItem))
                {

                    if (clickedFileItem.IsSelected)
                    {
                        _selectedItems.Add(clickedFileItem);
                    }
                    else
                    {
                        _selectedItems.Remove(clickedFileItem);
                    }
                }
            }
            if (clickedFileItem != null && (Keyboard.IsKeyDown(Key.LeftShift) || Keyboard.IsKeyDown(Key.RightShift))
                && !((Keyboard.IsKeyDown(Key.LeftAlt) || Keyboard.IsKeyDown(Key.RightAlt))))
            {
                int clickedIndex = FileItems.IndexOf(clickedFileItem);
                int minSelectedIndex = int.MaxValue;
                int maxSelectedIndex = -1;
                for (int i = 0; i < FileItems.Count; i++)
                {
                    if (!FileItems[i].IsSelected) continue;
                    if (i == clickedIndex) continue;
                    maxSelectedIndex = i;
                    if (minSelectedIndex > i) minSelectedIndex = i;
                }
                int selectToIndex = Math.Abs(clickedIndex - minSelectedIndex) <= Math.Abs(clickedIndex - maxSelectedIndex)
                                    ? minSelectedIndex
                                    : maxSelectedIndex;

                int start = Math.Min(clickedIndex, selectToIndex);
                int end = Math.Max(clickedIndex, selectToIndex);
                _selectedItems.Clear();

                for (int i = 0; i < FileItems.Count; i++)
                {
                    if (start <= i && i <= end)
                    {
                        FileItems[i].IsSelected = true;
                        _selectedItems.Add(FileItems[i]);
                    }
                    else
                    {
                        FileItems[i].IsSelected = false;
                    }
                }
            }
        }


        private void FileItem_RightClick(object sender, MouseButtonEventArgs e)
        {
            _canAutoClose = false;
            var clickedFileItem = (sender as Border)?.DataContext as FileItem;

            if (clickedFileItem != null)
            {
                clickedFileItem.IsSelected = true;
                if (_selectedItems.Count <= 1 && !_selectedItems.Contains(clickedFileItem))
                {
                    _selectedItems.Clear();
                    foreach (var fileItem in FileItems)
                    {
                        if (fileItem != clickedFileItem)
                        {
                            fileItem.IsSelected = false;
                        }
                    }
                    _selectedItems.Add(clickedFileItem);
                }
            }

            if (sender is Border border && border.DataContext is FileItem clickedItem)
            {
                var windowHelper = new WindowInteropHelper(this);


                FileInfo[] files = new FileInfo[1];
                files[0] = new FileInfo(clickedItem.FullPath!);

                Point cursorPosition = System.Windows.Forms.Cursor.Position;
                System.Windows.Point wpfPoint = new System.Windows.Point(cursorPosition.X, cursorPosition.Y);
                Point drawingPoint = new Point((int)wpfPoint.X, (int)wpfPoint.Y);
                _contextMenuIsOpen = true;
                Action renameHandler = null;
                scm.ContextMenuClosed += () =>
                {
                    _selectedItems.Clear();
                    foreach (var item in FileItems)
                    {
                        item.IsSelected = false;
                    }
                    _contextMenuIsOpen = false;
                };
                renameHandler = () =>
                {
                    try
                    {
                        if (clickedFileItem != null)
                        {
                            if (_itemCurrentlyRenaming != null)
                            {
                                _itemCurrentlyRenaming.IsRenaming = false;
                            }

                            _itemCurrentlyRenaming = clickedFileItem;
                            _itemCurrentlyRenaming.IsRenaming = true;
                            _isRenamingFromContextMenu = true;
                            DependencyObject container = FileWrapPanel.ItemContainerGenerator.ContainerFromItem(_itemCurrentlyRenaming);

                            var renameTextBox = FindParentOrChild<TextBox>(container);

                            renameTextBox!.Text = _itemCurrentlyRenaming.Name;
                            _isRenaming = true;
                            renameTextBox.Focus();

                            var text = renameTextBox.Text;
                            var dotIndex = text.LastIndexOf('.');
                            if (dotIndex <= 0) renameTextBox.SelectAll();
                            else renameTextBox.Select(0, dotIndex);
                            scm.ContextMenuRenameSelected -= renameHandler;
                        }
                    }
                    catch { }
                };
                scm.ContextMenuRenameSelected += renameHandler;
                if (clickedFileItem != null)
                {
                    if (_selectedItems.Count > 0 && _selectedItems.Contains(clickedItem))
                    {
                        files = _selectedItems.Where(item => item.IsSelected).Select(item => new FileInfo(item.FullPath!)).ToArray();
                    }
                    else
                    {
                        _selectedItems.Clear();
                    }
                    if (_itemCurrentlyRenaming != null)
                    {
                        _itemCurrentlyRenaming.IsRenaming = false;
                    }
                    if (_selectedItems.Count > 1)
                    {
                        scm.ShowContextMenu(windowHelper.Handle, files, drawingPoint, true);
                    }
                    else
                    {
                        scm.ShowContextMenu(windowHelper.Handle, files, drawingPoint, (clickedFileItem!.FullPath == _currentFolderPath));
                    }
                }
            }
        }

        private void Window_DragLeave(object sender, DragEventArgs e)
        {
            if (_isMinimized)
            {
                AnimateWindowHeight(titleBar.Height, Instance.AnimationSpeed);
            }
            if (!IsCursorWithinWindowBounds() && !_isDragging)
            {
                AnimateActiveColor(Instance.AnimationSpeed);
                if (Instance.HideTitleBarIconsWhenInactive)
                {
                    TitleBarIconsFadeAnimation(true);
                }
            }
            AnimateWindowOpacity(Instance.IdleOpacity, Instance.AnimationSpeed);
            _dragdropIntoFolder = false;
        }
        private void Window_DragOver(object sender, DragEventArgs e)
        {
            if (e.Data.GetDataPresent("Shell IDList Array") ||
                e.Data.GetDataPresent(DataFormats.FileDrop) ||
                e.Data.GetDataPresent(DataFormats.Text) ||
                e.Data.GetDataPresent(DataFormats.UnicodeText) ||
                e.Data.GetDataPresent("FileGroupDescriptorW") ||
                e.Data.GetDataPresent("FileGroupDescriptor"))
            {
                e.Effects = DragDropEffects.Copy | DragDropEffects.Link;
                e.Handled = true;
            }
        }

        private void Window_DragEnter(object sender, DragEventArgs e)
        {
            if (e.Data.GetDataPresent("Shell IDList Array") ||
                e.Data.GetDataPresent(DataFormats.FileDrop) ||
                e.Data.GetDataPresent(DataFormats.Text) ||
                e.Data.GetDataPresent(DataFormats.UnicodeText) ||
                e.Data.GetDataPresent("FileGroupDescriptorW") ||
                e.Data.GetDataPresent("FileGroupDescriptor"))
            {
                e.Effects = DragDropEffects.Copy | DragDropEffects.Link;
            }

            if (!_mouseIsOver && IsCursorWithinWindowBounds())
            {
                AnimateActiveColor(Instance.AnimationSpeed);
                if (Instance.HideTitleBarIconsWhenInactive)
                {
                    TitleBarIconsFadeAnimation(true);
                }
            }
            AnimateWindowHeight(Instance.Height, Instance.AnimationSpeed); AnimateWindowOpacity(1, Instance.AnimationSpeed);
            var sourceElement = e.OriginalSource as DependencyObject;
            var currentBorder = new Border();
            if (showFolderInGrid.Visibility == Visibility.Visible)
            {
                currentBorder = sourceElement as Border ?? FindParentOrChild<Border>(sourceElement);
            }
            else
            {
                currentBorder = sourceElement as Border ?? FindParent<Border>(sourceElement);
            }
            _dragdropIntoFolder = true;
            if (currentBorder != _lastBorder)
            {
                if (_lastBorder != null)
                {
                    // _isDragging = true;
                    FileItem_MouseLeave(_lastBorder, null);
                }
                _lastBorder = currentBorder;
            }
            if (currentBorder != null)
            {
                FileItem_MouseEnter(currentBorder, null);
            }
        }
        private T? FindParentOrChild<T>(DependencyObject element) where T : DependencyObject
        {
            if (element is T targetElement) return targetElement;
            for (int i = 0; i < VisualTreeHelper.GetChildrenCount(element); i++)
            {
                var child = VisualTreeHelper.GetChild(element, i);
                if (child is T childElement) return childElement;

                var nestedChild = FindParentOrChild<T>(child);
                if (nestedChild != null) return nestedChild;
            }
            return FindParent<T>(element);
        }

        private T? FindParent<T>(DependencyObject child) where T : DependencyObject
        {
            DependencyObject parent = VisualTreeHelper.GetParent(child);
            while (parent != null && !(parent is T))
            {
                parent = VisualTreeHelper.GetParent(parent);
            }
            return parent as T;
        }
        private void ListViewItem_Selected(object sender, RoutedEventArgs e)
        {
            if (sender is ListViewItem item && item.DataContext is FileItem fileItem)
            {
                fileItem.IsSelected = true;
            }
        }
        private void ListViewItem_Unselected(object sender, RoutedEventArgs e)
        {
            if (sender is ListViewItem item && item.DataContext is FileItem fileItem)
            {
                fileItem.IsSelected = false;
                var sourceElement = e.OriginalSource as DependencyObject;
                var currentBorder = sourceElement as Border ?? FindParentOrChild<Border>(sourceElement);
                if (currentBorder != null) currentBorder.Background = Brushes.Transparent;
            }
        }
        private void ListViewItem_MouseEnter(object sender, MouseEventArgs e)
        {
            _dropIntoFolderPath = "";

            if (sender is ListViewItem item && item.DataContext is FileItem fileItem)
            {
                _itemUnderCursor = fileItem;
                var sourceElement = e.OriginalSource as DependencyObject;
                var currentBorder = sourceElement as Border ?? FindParentOrChild<Border>(sourceElement);

                if (currentBorder != null)
                {
                    if (!fileItem.IsSelected)
                    {
                        currentBorder.Background = new SolidColorBrush(Color.FromArgb(15, 255, 255, 255));
                    }
                }
            }
        }
        private void ListViewItem_MouseLeave(object sender, MouseEventArgs e)
        {
            _dropIntoFolderPath = "";
            if (sender is ListViewItem item && item.DataContext is FileItem fileItem)
            {
                _itemUnderCursor = null;
                if (!_isRenamingFromContextMenu)
                {
                    fileItem.IsRenaming = false;
                    _isRenaming = false;
                }
                if (Instance.ShowInGrid)
                {
                    Keyboard.ClearFocus(); // Remove focus border
                }
                var sourceElement = e.OriginalSource as DependencyObject;
                var currentBorder = sourceElement as Border ?? FindParentOrChild<Border>(sourceElement);

                if (currentBorder != null)
                {
                    if (!fileItem.IsSelected)
                    {
                        currentBorder.Background = Brushes.Transparent;
                    }
                }
            }
        }
        private void FileItem_MouseEnter(object sender, MouseEventArgs? e)
        {
            if (sender is Border border && border.DataContext is FileItem fileItem)
            {
                _itemUnderCursor = fileItem;
                if (Instance.EnableCustomItemsOrder && ((GetAsyncKeyState(0xA4) & 0x8000) != 0 ||
                    (GetAsyncKeyState(0xA5) & 0x8000) != 0)) // Left or right ALT is down
                {
                    //  fileItem.Background = new SolidColorBrush(Color.FromArgb(30, 255, 255, 255));
                    _canChangeItemPosition = true;
                }
                else
                {
                    _canChangeItemPosition = false;
                }

                if (_canChangeItemPosition && _isDragging && !fileItem.IsSelected)
                {
                    fileItem.Background = new SolidColorBrush(Color.FromArgb(30, 255, 255, 255));

                    fileItem.IsMoveBarVisible = true;
                }
                else
                {
                    fileItem.IsMoveBarVisible = false;
                }
                if (_dragdropIntoFolder && fileItem.IsFolder && !_canChangeItemPosition)
                {
                    _dropIntoFolderPath = fileItem.FullPath + "\\";
                    if (showFolderInGrid.Visibility == Visibility.Visible)
                    {
                        border.Background = new SolidColorBrush(Color.FromArgb(15, 255, 255, 255));
                    }
                    else
                    {
                        fileItem.Background = new SolidColorBrush(Color.FromArgb(30, 255, 255, 255));
                    }
                }
                else if (!_dragdropIntoFolder)
                {
                    if (showFolderInGrid.Visibility == Visibility.Visible)
                    {
                        border.Background = fileItem.IsSelected ? new SolidColorBrush(Color.FromArgb(15, 255, 255, 255)) : Brushes.Transparent;
                    }
                    else
                    {
                        fileItem.Background = new SolidColorBrush(Color.FromArgb(30, 255, 255, 255));
                    }
                }
                if (showFolderInGrid.Visibility == Visibility.Visible && !fileItem.IsSelected && fileItem.IsFolder)
                {
                    border.Background = new SolidColorBrush(Color.FromArgb(30, 255, 255, 255));
                }
            }
        }

        private void FileItem_MouseLeave(object sender, MouseEventArgs? e)
        {
            if (sender is Border border && border.DataContext is FileItem fileItem)
            {
                _itemUnderCursor = null;
                if (!_isRenamingFromContextMenu)
                {
                    fileItem.IsRenaming = false;
                    _isRenaming = false;
                }
                fileItem.IsMoveBarVisible = false;
                _dropIntoFolderPath = "";
                if (!fileItem.IsSelected)
                {
                    fileItem.Background = fileItem.IsSelected ? new SolidColorBrush(Color.FromArgb(30, 255, 255, 255)) : Brushes.Transparent;
                }
                else
                {
                    fileItem.Background = new SolidColorBrush(Color.FromArgb(50, 255, 255, 255));
                }
                if (showFolderInGrid.Visibility == Visibility.Visible && !fileItem.IsSelected /*&& !fileItem.IsFolder*/)
                {
                    border.Background = fileItem.IsSelected ? new SolidColorBrush(Color.FromArgb(15, 255, 255, 255)) : Brushes.Transparent;
                }
            }
        }

        public BitmapSource? GetThumbnail(string filePath, int size)
        {
            return GetThumbnailInternal(filePath, size);
        }

        public static BitmapSource? GetThumbnailInternal(string filePath, int size)
        {
            try
            {
                using (ShellObject shellObject = ShellObject.FromParsingName(filePath))
                {
                    ShellThumbnail shellThumbnail = shellObject.Thumbnail;
                    shellThumbnail.CurrentSize = new System.Windows.Size(size, size);
                    BitmapSource thumbnail = shellThumbnail.BitmapSource;
                    thumbnail.Freeze();
                    return thumbnail;
                }
            }
            catch
            {
                return null;
            }
        }

        private static BitmapSource? GetThumbnailWithOverlay(string path, int iconSize, bool showShortcutArrow, double windowsScalingFactor)
        {
            var thumbnail = GetThumbnailInternal(path, iconSize);
            if (thumbnail == null) return null;

            if (showShortcutArrow)
            {
                try
                {
                    IntPtr[] overlayIcons = new IntPtr[1];
                    int overlayExtracted = ExtractIconEx(
                        Environment.SystemDirectory + "\\shell32.dll",
                        29,
                        overlayIcons,
                        null,
                        1);

                    if (overlayExtracted > 0 && overlayIcons[0] != IntPtr.Zero)
                    {
                        var overlay = Imaging.CreateBitmapSourceFromHIcon(
                                      overlayIcons[0],
                                      Int32Rect.Empty,
                                      BitmapSizeOptions.FromEmptyOptions());
                        overlay.Freeze();
                        DestroyIcon(overlayIcons[0]);

                        var visual = new DrawingVisual();
                        using (var dc = visual.RenderOpen())
                        {
                            double scale = iconSize / Math.Max(thumbnail.PixelWidth, thumbnail.PixelHeight);
                            double thumbnailWidth = thumbnail.PixelWidth * scale;
                            double thumbnailHeight = thumbnail.PixelHeight * scale;

                            double thumbnailX = (iconSize - thumbnailWidth) / 2.0;
                            double thumbnailY = (iconSize - thumbnailHeight) / 2.0;

                            dc.DrawImage(
                                thumbnail,
                                new Rect(
                                    thumbnailX,
                                    thumbnailY,
                                    thumbnailWidth,
                                    thumbnailHeight)
                            );
                            double overlayScale = (iconSize < 32 ? iconSize / 32.0 : 1.0);
                            if (windowsScalingFactor != 1.0)
                            {
                                overlayScale *= (1 / windowsScalingFactor);
                            }
                            if (overlayScale != 1.0)
                            {
                                overlay = new TransformedBitmap(overlay, new ScaleTransform(overlayScale, overlayScale));
                                overlay.Freeze();
                            }
                            double overlayX = thumbnailX;
                            double overlayY = thumbnailY + thumbnailHeight - overlay.PixelHeight;
                            dc.DrawImage(overlay,
                                new Rect(
                                overlayX,
                                overlayY,
                                overlay.PixelWidth,
                                overlay.PixelHeight)
                            );
                        }

                        var rtb = new RenderTargetBitmap(
                            iconSize,
                            iconSize,
                            thumbnail.DpiX,
                            thumbnail.DpiY,
                            PixelFormats.Pbgra32);
                        rtb.Render(visual);
                        rtb.Freeze();
                        return rtb;
                    }
                }
                catch (Exception ex)
                {
                    Debug.WriteLine("Failed to extract or render shortcut overlay: " + ex.Message);
                }
            }

            return thumbnail;
        }

        private async Task<BitmapSource?> GetThumbnailAsync(string path)
        {
            if (string.IsNullOrWhiteSpace(path)) return null;

            // Lấy thời điểm sửa đổi của file làm cache key
            DateTime lastWrite;
            try
            {
                lastWrite = File.Exists(path) ? File.GetLastWriteTime(path) : Directory.Exists(path) ? Directory.GetLastWriteTime(path) : DateTime.MinValue;
            }
            catch
            {
                lastWrite = DateTime.MinValue;
            }

            int iconSize = (int)(Instance.IconSize * _windowsScalingFactor);
            var cacheKey = (Path: path.ToLowerInvariant(), Size: iconSize, LastWrite: lastWrite);

            // Kiểm tra cache
            if (_thumbnailCache.TryGetValue(cacheKey, out var cachedThumbnail))
            {
                return cachedThumbnail;
            }

            // Xử lý nạp thumbnail mới
            BitmapSource? thumbnail = null;
            if (Path.GetExtension(path).ToLower() == ".svg")
            {
                try
                {
                    thumbnail = await LoadSvgThumbnailAsync(path, iconSize);
                }
                catch (Exception e)
                {
                    Debug.WriteLine(e);
                }
            }
            else
            {
                string ext = Path.GetExtension(path).ToLowerInvariant();
                bool isLink = ext == ".lnk" || ext == ".url";

                var request = new ThumbnailRequest
                {
                    Path = path,
                    Size = iconSize,
                    IsShortcut = isLink,
                    ShowShortcutArrow = Instance.ShowShortcutArrow,
                    WindowsScalingFactor = _windowsScalingFactor
                };

                _thumbnailQueue.Add(request);
                try
                {
                    thumbnail = await request.Tcs.Task;
                }
                catch (Exception e)
                {
                    Debug.WriteLine("Error fetching thumbnail from STA thread: " + e.Message);
                }
            }

            // Ghi vào cache nếu lấy thành công
            if (thumbnail != null)
            {
                _thumbnailCache[cacheKey] = thumbnail;
            }

            return thumbnail;
        }



        private async Task<BitmapSource?> LoadSvgThumbnailAsync(string path, int iconSize)
        {
            return await Task.Run(() =>
            {
                try
                {
                    var svgDocument = Svg.SvgDocument.Open(path);

                    using (var bitmap = svgDocument.Draw(iconSize, iconSize))
                    {
                        using (var ms = new MemoryStream())
                        {
                            bitmap.Save(ms, System.Drawing.Imaging.ImageFormat.Png);
                            ms.Seek(0, SeekOrigin.Begin);

                            var bitmapImage = new BitmapImage();
                            bitmapImage.BeginInit();
                            bitmapImage.StreamSource = ms;
                            bitmapImage.DecodePixelWidth = 64;
                            bitmapImage.DecodePixelHeight = 64;
                            bitmapImage.CacheOption = BitmapCacheOption.OnLoad;
                            bitmapImage.EndInit();
                            bitmapImage.Freeze();
                            return (BitmapSource)bitmapImage;
                        }
                    }
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"Failed to load SVG thumbnail: {ex.Message}");
                    return null;
                }
            });
        }
        public async Task<BitmapSource?> LoadUrlIconAsync(string path)
        {
            try
            {
                string iconFile = "";
                int iconIndex = 0;
                bool hasHttp = false;
                bool hasHttps = false;
                foreach (var line in File.ReadAllLines(path))
                {
                    // Debug.WriteLine(line);
                    if (line.StartsWith("IconFile=", StringComparison.OrdinalIgnoreCase))
                    {
                        iconFile = line.Substring("IconFile=".Length).Trim();
                    }
                    else if (line.StartsWith("IconIndex=", StringComparison.OrdinalIgnoreCase))
                    {
                        if (int.TryParse(line.Substring("IconIndex=".Length).Trim(), out int i))
                        {
                            iconIndex = i;
                        }
                    }
                    else if (iconFile == "")
                    {
                        if (line.StartsWith("URL=http://"))
                        {
                            hasHttp = true;
                            break;
                        }
                        else if (line.StartsWith("URL=https://"))
                        {
                            hasHttps = true;
                            break;
                        }
                    }
                }
                if (iconFile == "")
                {
                    if (hasHttp)
                    {
                        iconFile = GetDefaultBrowserPath("http");
                    }
                    else if (hasHttps)
                    {
                        iconFile = GetDefaultBrowserPath("https");
                    }
                }
                if (!string.IsNullOrEmpty(iconFile) && File.Exists(iconFile))
                {
                    return await Task.Run(() =>
                    {
                        IntPtr[] icons = new IntPtr[1];
                        int extracted = Interop.ExtractIconEx(iconFile, iconIndex, icons, null, 1);
                        if (extracted > 0 && icons[0] != IntPtr.Zero)
                        {
                            var source = Imaging.CreateBitmapSourceFromHIcon(
                                icons[0],
                                Int32Rect.Empty,
                                BitmapSizeOptions.FromEmptyOptions());
                            Interop.DestroyIcon(icons[0]);
                            if (Instance.ShowShortcutArrow)
                            {
                                IntPtr[] overlayIcons = new IntPtr[1];
                                int overlayExtracted = Interop.ExtractIconEx(
                                    Environment.SystemDirectory + "\\shell32.dll",
                                    29,
                                    overlayIcons,
                                    null,
                                    1);

                                if (overlayExtracted > 0 && overlayIcons[0] != IntPtr.Zero)
                                {
                                    var overlay = Imaging.CreateBitmapSourceFromHIcon(
                                        overlayIcons[0],
                                        Int32Rect.Empty,
                                        BitmapSizeOptions.FromEmptyOptions());
                                    Interop.DestroyIcon(overlayIcons[0]);

                                    var visual = new DrawingVisual();
                                    using (var dc = visual.RenderOpen())
                                    {
                                        dc.DrawImage(source, new Rect(0, 0, source.PixelWidth, source.PixelHeight));
                                        dc.DrawImage(overlay, new Rect(
                                            source.PixelWidth - overlay.PixelWidth,
                                            source.PixelHeight - overlay.PixelHeight,
                                            overlay.PixelWidth,
                                            overlay.PixelHeight));
                                    }

                                    var rtb = new RenderTargetBitmap(
                                        source.PixelWidth,
                                        source.PixelHeight,
                                        source.DpiX,
                                        source.DpiY,
                                        PixelFormats.Pbgra32);
                                    rtb.Render(visual);
                                    rtb.Freeze();

                                    return rtb;
                                }
                            }
                            source.Freeze();
                            return source;
                        }
                        return null;
                    });
                }
                return null;
            }
            catch (Exception e)
            {
                Debug.WriteLine("Error loading URL icon: " + e.Message);
                return await GetThumbnailAsync(path);
            }
        }
        private string GetDefaultBrowserPath(string protocol)
        {
            try
            {
                using (RegistryKey key = Registry.CurrentUser.OpenSubKey(@$"Software\Microsoft\Windows\Shell\Associations\UrlAssociations\{protocol}\UserChoice"))
                {
                    if (key != null)
                    {
                        object progId = key.GetValue("Progid");

                        if (progId == null)
                        {
                            return "";
                        }
                        using (RegistryKey commandKey = Registry.ClassesRoot.OpenSubKey($@"{progId}\shell\open\command"))
                        {
                            if (commandKey != null)
                            {
                                object command = commandKey.GetValue("");

                                if (command == null)
                                {
                                    return "";
                                }
                                return Regex.Match(command.ToString()!, "^\"([^\"]+)\"").Groups[1].Value;
                            }
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                return "";
            }
            return "";
        }
        private void Window_Loaded(object sender, RoutedEventArgs e)
        {
            UpdateFileExtensionIcon();
            UpdateHiddenFilesIcon();
            UpdateIconVisibility();
            AnimateChevron(_isMinimized, true, 0.01); // When 0 docked window won't open
            KeepWindowBehind();
            RegistryHelper rgh = new RegistryHelper("DeskFrame");
            bool toBlur = true;
            //if (rgh.KeyExistsRoot("blurBackground"))
            //{
            //    toBlur = (bool)rgh.ReadKeyValueRoot("blurBackground");
            //}
            // BackgroundType(toBlur);
        }

        public void ChangeBackgroundOpacity(int num)
        {
            try
            {
                var c = (Color)System.Windows.Media.ColorConverter.ConvertFromString(Instance.ListViewBackgroundColor);
                WindowBackground.Background = new SolidColorBrush(Color.FromArgb((byte)Instance.Opacity, c.R, c.G, c.B));
            }
            catch
            {

            }
        }
        public void ChangeIsBlack(bool value)
        {
            _isBlack = value;
        }
        public void BackgroundType(bool toBlur)
        {
            var hwnd = new WindowInteropHelper(this).Handle;
            var accent = new Interop.AccentPolicy
            {
                AccentState = toBlur ? Interop.AccentState.ACCENT_ENABLE_BLURBEHIND :
                                       Interop.AccentState.ACCENT_DISABLED
            };

            var data = new Interop.WindowCompositionAttributeData
            {
                Attribute = Interop.WindowCompositionAttribute.WCA_ACCENT_POLICY,
                SizeOfData = Marshal.SizeOf(accent),
                Data = Marshal.AllocHGlobal(Marshal.SizeOf(accent))
            };

            Marshal.StructureToPtr(accent, data.Data, false);
            Interop.SetWindowCompositionAttribute(hwnd, ref data);
            Marshal.FreeHGlobal(data.Data);
        }



        private void Window_MouseMove(object sender, MouseEventArgs e)
        {
            // Drag threshold: only start drag after mouse moves far enough from the click point
            if (_pendingDragItem != null && _pendingDragBorder != null)
            {
                if (e.LeftButton == MouseButtonState.Pressed)
                {
                    System.Windows.Point currentPos = e.GetPosition(this);
                    double deltaX = Math.Abs(currentPos.X - _dragStartPoint.X);
                    double deltaY = Math.Abs(currentPos.Y - _dragStartPoint.Y);

                    if (deltaX > SystemParameters.MinimumHorizontalDragDistance ||
                        deltaY > SystemParameters.MinimumVerticalDragDistance)
                    {
                        // Threshold exceeded — start the actual drag
                        var dragItem = _pendingDragItem;
                        var dragBorder = _pendingDragBorder;
                        _pendingDragItem = null;
                        _pendingDragBorder = null;
                        _isDragging = true;

                        DataObject data = new DataObject(DataFormats.FileDrop, new string[] { dragItem.FullPath! });
                        DragDrop.DoDragDrop(dragBorder, data, DragDropEffects.Copy | DragDropEffects.Move);
                    }
                }
                else
                {
                    // Mouse button released without moving — cancel pending drag (it was just a click)
                    _pendingDragItem = null;
                    _pendingDragBorder = null;
                }
            }

            var cursorPos = System.Windows.Forms.Cursor.Position;
            var windowPos = this.PointToScreen(new System.Windows.Point(0, 0));
            var windowWidth = this.ActualWidth;
            var windowHeight = this.ActualHeight;
            if (cursorPos.X - 10 < windowPos.X || cursorPos.X + 10 > windowPos.X + windowWidth ||
                cursorPos.Y - 10 < windowPos.Y || cursorPos.Y + 10 > windowPos.Y + windowHeight)
            {
                if (!_contextMenuIsOpen && !_mouseIsOver)
                {
                    _selectedItems.Clear();
                    foreach (var fileItem in FileItems)
                    {
                        fileItem.IsSelected = false;
                        fileItem.Background = Brushes.Transparent;
                    }
                }
            }
        }

        private void Window_LocationChanged(object sender, EventArgs e)
        {
            if (_isLeftButtonDown)
            {
                Instance.PosX = this.Left;
                Instance.PosY = this.Top;
            }
        }
        private void MainWindow_Loaded(object sender, RoutedEventArgs e)
        {
            KeepWindowBehind();
            //WindowChrome.SetWindowChrome(this, Instance.IsLocked ?
            //new WindowChrome
            //{
            //    ResizeBorderThickness = new Thickness(0),
            //    CaptionHeight = 0
            //}
            //: _isOnBottom ?
            //    new WindowChrome
            //    {
            //        GlassFrameThickness = new Thickness(5),
            //        CaptionHeight = 0,
            //        ResizeBorderThickness = new Thickness(0, Instance.Minimized ? 0 : 5, 5, 0),
            //        CornerRadius = new CornerRadius(5)
            //    } :
            //    new WindowChrome
            //    {
            //        GlassFrameThickness = new Thickness(5),
            //        CaptionHeight = 0,
            //        ResizeBorderThickness = new Thickness(5, 0, 5, Instance.Minimized ? 0 : 5),
            //        CornerRadius = new CornerRadius(5)
            //    }
            //);
            HandleWindowMove(true);
            try
            {

                _currentVD = Array.IndexOf(VirtualDesktop.GetDesktops(), VirtualDesktop.Current) + 1;
                Debug.WriteLine($"Start to desktop number: {_currentVD}");
                if (Instance.ShowOnVirtualDesktops != null && Instance.ShowOnVirtualDesktops.Length != 0 && !Instance.ShowOnVirtualDesktops.Contains(_currentVD))
                {
                    this.Hide();
                }
                else
                {
                    this.Show();
                }
                VirtualDesktop.CurrentChanged += (sender, args) =>
                {
                    var newDesktop = args.NewDesktop;
                    _currentVD = Array.IndexOf(VirtualDesktop.GetDesktops(), newDesktop) + 1;
                    if (Instance.ShowOnVirtualDesktops != null && Instance.ShowOnVirtualDesktops.Length != 0 && !Instance.ShowOnVirtualDesktops.Contains(_currentVD))
                    {
                        Dispatcher.InvokeAsync(() =>
                        {
                            this.Hide();
                        });
                    }
                    else
                    {
                        Dispatcher.InvokeAsync(() =>
                        {
                            this.Show();
                        });
                    }
                    Debug.WriteLine($"Switched to virtual desktop: {_currentVD}");
                };
                VirtualDesktopSupported = true;
            }
            catch
            {
                VirtualDesktopSupported = false;
            }
            if (Instance.Folder == "empty")
            {
                ParticleCanvas.Margin = new Thickness(0, titleBar.Height + 10, 0, 0);
                CompositionTarget.Rendering += UpdateParticle!;
            }
            else
            {
                ParticleCanvas.Visibility = Visibility.Hidden;
            }
        }

        private void UpdateParticle(object sender, EventArgs e)
        {
            double cx = ParticleCanvas.ActualWidth / 2;
            double cy = (ParticleCanvas.ActualHeight + titleBar.Height) / 2;

            if (_dragdropIntoFolder && Instance.Folder == "empty")
            {
                for (int i = 0; i < 20 && particles.Count < 20; i++)
                {
                    CreateParticle();
                }
            }
            else if (Instance.Folder != "empty" && particles.Count == 0)
            {
                CompositionTarget.Rendering -= UpdateParticle;
                ParticleCanvas.Visibility = Visibility.Hidden;
            }

            for (int i = particles.Count - 1; i >= 0; i--)
            {
                Particle p = particles[i];
                p.Update(cx, cy, 400);
                Ellipse v = visuals[i];
                v.Opacity = p.Opacity;
                Canvas.SetLeft(v, p.X);
                Canvas.SetTop(v, p.Y);

                if (!p.ToRemove)
                {
                    ParticleCanvas.Children.Remove(v);
                    visuals.RemoveAt(i);
                    particles.RemoveAt(i);
                }
            }
        }
        private void CreateParticle()
        {
            Particle p = new Particle(ParticleCanvas.ActualWidth, ParticleCanvas.ActualHeight);
            particles.Add(p);

            Ellipse e = new Ellipse
            {
                Width = 6,
                Height = 6,
                Opacity = 1,
                Fill = new RadialGradientBrush
                {
                    GradientStops =
                    {
                        new GradientStop(Colors.White, 0.0),
                        new GradientStop(Colors.White, 0.6),
                        new GradientStop(Colors.Transparent, 1.0)
                    }
                }
            };
            visuals.Add(e);
            ParticleCanvas.Children.Add(e);
        }

        private void MainWindow_SourceInitialized(object sender, EventArgs e)
        {
            _previousHeight = Instance.Height;
            KeepWindowBehind();
        }

        private void UpdateIcons()
        {
            nameMenuItem.Icon = (Instance.SortBy == 1 || Instance.SortBy == 2)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            dateModifiedMenuItem.Icon = (Instance.SortBy == 3 || Instance.SortBy == 4)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            dateCreatedMenuItem.Icon = (Instance.SortBy == 5 || Instance.SortBy == 6)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            fileTypeMenuItem.Icon = (Instance.SortBy == 7 || Instance.SortBy == 8)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            fileSizeMenuItem.Icon = (Instance.SortBy == 9 || Instance.SortBy == 10)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            ascendingMenuItem.Icon = (Instance.SortBy % 2 != 0)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            descendingMenuItem.Icon = (Instance.SortBy % 2 == 0)
                ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };

            if (folderNoneMenuItem != null)
            {
                folderNoneMenuItem.Icon = (Instance.FolderOrder == 0)
                    ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                    : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };
            }
            if (folderFirstMenuItem != null)
            {
                folderFirstMenuItem.Icon = (Instance.FolderOrder == 1)
                    ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                    : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };
            }
            if (folderLastMenuItem != null)
            {
                folderLastMenuItem.Icon = (Instance.FolderOrder == 2)
                    ? new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Filled = true }
                    : new SymbolIcon { Symbol = SymbolRegular.CircleSmall20, Foreground = Brushes.Transparent };
            }
        }
        private void titleBar_MouseRightButtonDown(object sender, MouseButtonEventArgs e)
        {
            contextMenu = new ContextMenu();
            if (_itemCurrentlyRenaming != null)
            {
                _itemCurrentlyRenaming.IsRenaming = false;
            }
            ToggleSwitch toggleHiddenFiles = new ToggleSwitch { Content = Lang.TitleBarContextMenu_HiddenFiles };
            toggleHiddenFiles.Click += (s, args) => { ToggleHiddenFiles(); LoadFiles(_currentFolderPath); };

            ToggleSwitch toggleFileExtension = new ToggleSwitch { Content = Lang.TitleBarContextMenu_FileExtensions };
            toggleFileExtension.Click += (_, _) => { ToggleFileExtension(); LoadFiles(_currentFolderPath); };

            toggleHiddenFiles.IsChecked = Instance.ShowHiddenFiles;
            toggleFileExtension.IsChecked = Instance.ShowFileExtension;

            MenuItem frameSettings = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_FrameSettings,
                Height = 34,
                Icon = new SymbolIcon(SymbolRegular.Settings20)
            };
            frameSettings.Click += (s, args) =>
            {
                bool itWasMin = _isMinimized;
                if (itWasMin)
                {
                    Minimize_MouseLeftButtonDown(null, null);
                }
                var dialog = new FrameSettingsDialog(this);
                dialog.ShowDialog();
                if (dialog.DialogResult == true)
                {
                    if (itWasMin)
                    {
                        Minimize_MouseLeftButtonDown(null, null);
                    }
                    LoadFiles(_currentFolderPath);
                }
            };

            MenuItem reloadItems = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_Reload,
                Height = 34,
                Icon = new SymbolIcon(SymbolRegular.ArrowSync20)
            };
            reloadItems.Click += (s, args) =>
            {
                FileItems.Clear();
                LoadFiles(Instance.Folder);
                _currentFolderPath = Instance.Folder;
                InitializeFileWatchers();

            };
            reloadItems.Visibility = (Instance.Folder == "empty" || string.IsNullOrEmpty(Instance.Folder)) ? Visibility.Collapsed : Visibility.Visible;

            MenuItem lockFrame = new MenuItem
            {
                Header = Instance.IsLocked ? Lang.TitleBarContextMenu_UnlockFrame : Lang.TitleBarContextMenu_LockFrame,
                Height = 34,
                Icon = Instance.IsLocked ? new SymbolIcon(SymbolRegular.LockClosed20) : new SymbolIcon(SymbolRegular.LockOpen20)
            };
            lockFrame.Click += (s, args) =>
            {
                _isLocked = !_isLocked;
                ToggleIsLocked();
                //WindowChrome.SetWindowChrome(this, Instance.IsLocked ?
                //new WindowChrome
                //{
                //    ResizeBorderThickness = new Thickness(0),
                //    CaptionHeight = 0
                //}
                //: _isOnBottom ?
                //    new WindowChrome
                //    {
                //        GlassFrameThickness = new Thickness(5),
                //        CaptionHeight = 0,
                //        ResizeBorderThickness = new Thickness(5, Instance.Minimized ? 0 : 5, 5, 0),
                //        CornerRadius = new CornerRadius(5)
                //    } :
                //    new WindowChrome
                //    {
                //        GlassFrameThickness = new Thickness(5),
                //        CaptionHeight = 0,
                //        ResizeBorderThickness = new Thickness(5, 0, 5, Instance.Minimized ? 0 : 5),
                //        CornerRadius = new CornerRadius(5)
                //    }
                //);

            };

            MenuItem exitItem = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_Remove,
                Height = 34,
                Foreground = new SolidColorBrush((Color)ColorConverter.ConvertFromString("#FFFC6060")),
                Icon = new SymbolIcon(SymbolRegular.Delete20)

            };

            exitItem.Click += async (s, args) =>
            {
                var dialog = new MessageBox
                {
                    Title = Lang.TitleBarContextMenu_RemoveMessageBox_Title,
                    Content = Lang.TitleBarContextMenu_RemoveMessageBox_Content,
                    PrimaryButtonText = Lang.TitleBarContextMenu_RemoveMessageBox_Yes,
                    CloseButtonText = Lang.TitleBarContextMenu_RemoveMessageBox_No
                };

                var result = await dialog.ShowDialogAsync();

                if (result == MessageBoxResult.Primary)
                {
                    RegistryKey key = Registry.CurrentUser.OpenSubKey(Instance.GetKeyLocation(), true)!;
                    if (key != null)
                    {
                        Registry.CurrentUser.DeleteSubKeyTree(Instance.GetKeyLocation());
                    }
                    MainWindow._controller.RemoveInstance(Instance, this);
                    if (Instance.IsShortcutsOnly)
                    {
                        Directory.Delete(Instance.Folder, true);
                    }
                    this.Close();

                }
            };

            MenuItem sortByMenuItem = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_Sortby,
                Height = 34,
                Icon = new SymbolIcon(SymbolRegular.ArrowSort20)
            };
            nameMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_Name, Height = 34, StaysOpenOnClick = true };
            dateModifiedMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_DateModified, Height = 34, StaysOpenOnClick = true };
            dateCreatedMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_DateCreated, Height = 34, StaysOpenOnClick = true };
            fileTypeMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_FileType, Height = 34, StaysOpenOnClick = true };
            fileSizeMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_FileSize, Height = 34, StaysOpenOnClick = true };
            ascendingMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_Ascending, Height = 34, StaysOpenOnClick = true };
            descendingMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_Descending, Height = 34, StaysOpenOnClick = true };



            nameMenuItem.Click += async (s, args) =>
            {
                if (Instance.SortBy % 2 != 0 || Instance.SortBy != 1) Instance.SortBy = 1;
                else Instance.SortBy = 2;
                UpdateIcons();
                SortItems();
            };
            dateModifiedMenuItem.Click += async (s, args) =>
            {
                if (Instance.SortBy % 2 != 0 || Instance.SortBy != 3) Instance.SortBy = 3;
                else Instance.SortBy = 4;
                UpdateIcons();
                SortItems();
            };

            dateCreatedMenuItem.Click += async (s, args) =>
            {
                if (Instance.SortBy % 2 != 0 || Instance.SortBy != 5) Instance.SortBy = 5;
                else Instance.SortBy = 6;
                UpdateIcons();
                SortItems();
            };
            fileTypeMenuItem.Click += async (s, args) =>
            {
                if (Instance.SortBy % 2 != 0 || Instance.SortBy != 7) Instance.SortBy = 7;
                else Instance.SortBy = 8;
                UpdateIcons();
                SortItems();
            };
            fileSizeMenuItem.Click += (s, args) =>
            {
                if (Instance.SortBy % 2 != 0 && Instance.SortBy != 9) Instance.SortBy = 9;
                else Instance.SortBy = 10;
                UpdateIcons();
                SortItems();
            };

            ascendingMenuItem.Click += async (s, args) =>
            {
                if (Instance.SortBy % 2 == 0) Instance.SortBy -= 1;
                UpdateIcons();
                SortItems();
            };

            descendingMenuItem.Click += async (s, args) =>
            {
                if (Instance.SortBy % 2 != 0) Instance.SortBy += 1;
                UpdateIcons();
                SortItems();
            };

            MenuItem FrameInfoItem = new MenuItem
            {
                StaysOpenOnClick = true,
                IsEnabled = false,
            };
            TextBlock InfoText = new TextBlock
            {
                HorizontalAlignment = System.Windows.HorizontalAlignment.Left,
                VerticalAlignment = VerticalAlignment.Top,
                FontSize = 12,
                TextWrapping = TextWrapping.Wrap,
            };

            InfoText.Inlines.Add(new Run(Lang.TitleBarContextMenu_Info_Files) { Foreground = Brushes.White });
            InfoText.Inlines.Add(new Run($"{_fileCount}") { Foreground = Brushes.CornflowerBlue });
            InfoText.Inlines.Add(new Run("\n"));

            InfoText.Inlines.Add(new Run(Lang.TitleBarContextMenu_Info_Folders) { Foreground = Brushes.White });
            InfoText.Inlines.Add(new Run($"{_folderCount}") { Foreground = Brushes.CornflowerBlue });
            InfoText.Inlines.Add(new Run("\n"));
            if (Instance.CheckFolderSize)
            {
                InfoText.Inlines.Add(new Run(Lang.TitleBarContextMenu_Info_FolderSize) { Foreground = Brushes.White });
                InfoText.Inlines.Add(new Run($"{_folderSize}") { Foreground = Brushes.CornflowerBlue });
                InfoText.Inlines.Add(new Run("\n"));
            }

            InfoText.Inlines.Add(new Run(Lang.TitleBarContextMenu_Info_LastUpdated) { Foreground = Brushes.White });
            InfoText.Inlines.Add(new Run($"{_lastUpdated.ToString("hh:mm tt")}") { Foreground = Brushes.CornflowerBlue });

            FrameInfoItem.Header = InfoText;

            CustomItemOrderMenuItem = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_CustomItemOrder,
                Height = 36,
                StaysOpenOnClick = true,
                Icon = new SymbolIcon { Symbol = SymbolRegular.Star20 }
            };

            MenuItem CustomItemOrder_Delete_MenuItem = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_CustomItemOrder_DeleteOrder,
                Height = 34,
                Icon = new SymbolIcon { Symbol = SymbolRegular.Delete20 }
            };
            CustomItemOrder_Delete_MenuItem.Click += (s, args) =>
            {
                Instance.CustomOrderFiles = null;
                SortItems();
            };
            ToggleSwitch CustomItemOrder_ToggleSwitch = new ToggleSwitch
            {
                IsChecked = Instance.EnableCustomItemsOrder,
                Content = Instance.EnableCustomItemsOrder ? Lang.TitleBarContextMenu_CustomItemOrder_ToggleSwitch_Enable : Lang.TitleBarContextMenu_CustomItemOrder_ToggleSwitch_Disable,
                Height = 20,
            };
            CustomItemOrder_ToggleSwitch.Click += (s, args) =>
            {
                Instance.EnableCustomItemsOrder = !Instance.EnableCustomItemsOrder;
                CustomItemOrder_ToggleSwitch.Content = Instance.EnableCustomItemsOrder ?
                    Lang.TitleBarContextMenu_CustomItemOrder_ToggleSwitch_Enable : Lang.TitleBarContextMenu_CustomItemOrder_ToggleSwitch_Disable;
                SortItems();
            };
            CustomItemOrderMenuItem.Items.Add(CustomItemOrder_ToggleSwitch);
            CustomItemOrderMenuItem.Items.Add(CustomItemOrder_Delete_MenuItem);

            folderOrderMenuItem = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_Sortby_FolderOrder,
                Height = 36,
                StaysOpenOnClick = true,
                Icon = new SymbolIcon { Symbol = SymbolRegular.Folder20 }
            };

            folderNoneMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_FolderIder_None, Height = 34, StaysOpenOnClick = true };
            folderFirstMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_FolderIder_First, Height = 34, StaysOpenOnClick = true };
            folderLastMenuItem = new MenuItem { Header = Lang.TitleBarContextMenu_Sortby_FolderIder_Last, Height = 34, StaysOpenOnClick = true };

            folderNoneMenuItem.Click += (s, args) =>
            {
                Instance.FolderOrder = 0;
                UpdateIcons();
                SortItems();
            };
            folderFirstMenuItem.Click += (s, args) =>
            {
                Instance.FolderOrder = 1;
                UpdateIcons();
                SortItems();
            };
            folderLastMenuItem.Click += (s, args) =>
            {
                Instance.FolderOrder = 2;
                UpdateIcons();
                SortItems();
            };

            UpdateIcons();

            MenuItem openInExplorerMenuItem = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_OpenFolder,
                Icon = new SymbolIcon { Symbol = SymbolRegular.FolderOpen20 }
            };
            openInExplorerMenuItem.Visibility = (Instance.Folder == "empty" || string.IsNullOrEmpty(Instance.Folder)) ? Visibility.Collapsed : Visibility.Visible;
            openInExplorerMenuItem.Click += (_, _) => { OpenFolder(); };


            MenuItem changeItemView = new MenuItem
            {
                Header = Lang.TitleBarContextMenu_ChangeView
            };
            if (showFolder.Visibility == Visibility.Visible)
            {
                changeItemView.Header = Lang.TitleBarContextMenu_GridView;
                changeItemView.Icon = new SymbolIcon { Symbol = SymbolRegular.Grid20 };
            }
            else
            {
                changeItemView.Header = Lang.TitleBarContextMenu_DetailsView;
                changeItemView.Icon = new SymbolIcon { Symbol = SymbolRegular.AppsList20 };
            }
            changeItemView.Click += (_, _) =>
            {
                if (showFolder.Visibility == Visibility.Visible)
                {
                    changeItemView.Header = Lang.TitleBarContextMenu_GridView;
                    changeItemView.Icon = new SymbolIcon { Symbol = SymbolRegular.Grid20 };
                    showFolderInGrid.Visibility = Visibility.Visible;
                    showFolder.Visibility = Visibility.Hidden;
                    Instance.ShowInGrid = !Instance.ShowInGrid;
                }
                else
                {
                    Instance.ShowInGrid = !Instance.ShowInGrid;
                    showFolder.Visibility = Visibility.Visible;
                    showFolderInGrid.Visibility = Visibility.Hidden;
                    changeItemView.Header = Lang.TitleBarContextMenu_DetailsView;
                    changeItemView.Icon = new SymbolIcon { Symbol = SymbolRegular.AppsList20 };
                }
            };

            folderOrderMenuItem.Items.Add(folderNoneMenuItem);
            folderOrderMenuItem.Items.Add(folderFirstMenuItem);
            folderOrderMenuItem.Items.Add(folderLastMenuItem);


            sortByMenuItem.Items.Add(CustomItemOrderMenuItem);
            sortByMenuItem.Items.Add(folderOrderMenuItem);
            sortByMenuItem.Items.Add(new Separator());
            sortByMenuItem.Items.Add(nameMenuItem);
            sortByMenuItem.Items.Add(dateModifiedMenuItem);
            sortByMenuItem.Items.Add(dateCreatedMenuItem);
            sortByMenuItem.Items.Add(fileTypeMenuItem);
            sortByMenuItem.Items.Add(fileSizeMenuItem);
            sortByMenuItem.Items.Add(new Separator());
            sortByMenuItem.Items.Add(ascendingMenuItem);
            sortByMenuItem.Items.Add(descendingMenuItem);

            contextMenu.Items.Add(sortByMenuItem);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(lockFrame);
            contextMenu.Items.Add(reloadItems);
            contextMenu.Items.Add(openInExplorerMenuItem);
            contextMenu.Items.Add(changeItemView);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(toggleHiddenFiles);
            contextMenu.Items.Add(toggleFileExtension);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(frameSettings);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(FrameInfoItem);
            contextMenu.Items.Add(new Separator());
            contextMenu.Items.Add(exitItem);

            contextMenu.IsOpen = true;
        }

        private void Window_StateChanged(object sender, EventArgs e)
        {
            KeepWindowBehind();
            Debug.WriteLine("Window_StateChanged hide");
        }
        public Task<string> BytesToStringAsync(long byteCount)
        {
            return Task.Run(() =>
            {
                double kilobytes = byteCount / 1024.0;
                string formattedKilobytes;
                try
                {
                    formattedKilobytes = kilobytes.ToString("#,0", System.Globalization.CultureInfo.InvariantCulture).Replace(",", " ");
                }
                catch
                {
                    try
                    {
                        formattedKilobytes = kilobytes.ToString("#,0", System.Globalization.CultureInfo.CurrentCulture).Replace(",", " ");
                    }
                    catch
                    {
                        formattedKilobytes = kilobytes.ToString("#,0").Replace(",", " ");
                    }
                }
                return formattedKilobytes + " KB";
            });
        }

        private void FileListView_PreviewMouseUp(object sender, MouseButtonEventArgs e)
        {
            var point = e.GetPosition(FileListView);
            var hit = VisualTreeHelper.HitTest(FileListView, point)?.VisualHit;

            while (hit != null && hit is not GridViewColumnHeader)
                hit = VisualTreeHelper.GetParent(hit);

            if (hit is not GridViewColumnHeader header || header.Column == null)
                return;

            int newSort = Instance.SortBy;

            if (header.Column == NameGridColumn)
                newSort = Instance.SortBy != 1 ? 1 : 2;
            else if (header.Column == DateModifiedGridColumn)
                newSort = Instance.SortBy != 3 ? 3 : 4;
            else if (header.Column == SizeGridColumn)
                newSort = Instance.SortBy != 9 ? 9 : 10;

            if (newSort != Instance.SortBy)
            {
                Instance.SortBy = newSort;
                SortItems();
            }
        }

        private int GetZIndex(IntPtr hwnd)
        {
            IntPtr h = GetTopWindow(shellView);
            int z = 0;

            while (h != IntPtr.Zero)
            {
                if (h == hwnd) return z;
                h = Interop.GetWindow(h, GW_HWNDNEXT);
                z++;
            }
            return -1;
        }
        IntPtr GetWindowWithMinZIndex(List<IntPtr> windowHandles)
        {
            IntPtr lowestWindow = IntPtr.Zero;
            int lowestZ = int.MaxValue;

            foreach (var hwnd in windowHandles)
            {
                int z = 0;
                IntPtr prev = hwnd;

                while ((prev = Interop.GetWindow(prev, GW_HWNDPREV)) != IntPtr.Zero)
                {
                    z++;
                }

                if (z >= 0 && z < lowestZ)
                {
                    lowestZ = z;
                    lowestWindow = hwnd;
                }
            }
            return lowestWindow;
        }
        Rectangle RectToRectangle(RECT r)
        {
            return new Rectangle(
                r.Left,
                r.Top,
                r.Right - r.Left,
                r.Bottom - r.Top
            );
        }
        private bool WindowIsOverlapped(IntPtr hwnd, List<IntPtr> windowHandles)
        {
            if (!GetWindowRect(hwnd, out RECT thisR))
            {
                return false;
            }
            Rectangle thisRect = RectToRectangle(thisR);
            if (Instance.AutoExpandonCursor && _isMinimized)
            {
                thisRect = new Rectangle(
                    thisRect.Left,
                    thisRect.Top,
                    thisRect.Width,
                    (int)Instance.Height
                );
            }
            int zIndex = GetZIndex(hwnd);
            foreach (var window in windowHandles)
            {
                if (window == hwnd) continue;
                if (!GetWindowRect(window, out RECT testR)) continue;
                if (GetZIndex(window) > zIndex) continue;

                Rectangle testRect = RectToRectangle(testR);
                Rectangle intersect = Rectangle.Intersect(thisRect, testRect);
                if (intersect.Width > 0 && intersect.Height > 0)
                {
                    return true;
                }
            }
            return false;
        }

        void BringFrameToFront(IntPtr hwnd, bool forceToFront)
        {
            IntPtr hwndLower = GetWindowWithMinZIndex(MainWindow._controller._subWindowsPtr);
            bool overlapped = WindowIsOverlapped(hwnd, MainWindow._controller._subWindowsPtr);

            if (forceToFront || (hwnd != hwndLower && overlapped))
            {
                hwndLower = Interop.GetWindow(hwndLower, GW_HWNDPREV);
                SendMessage(hwnd, WM_SETREDRAW, 0, IntPtr.Zero);
                Debug.WriteLine("moved to the front");
                SetWindowPos(hwnd, 0, 0, 0, 0, 0,
               SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_NOOWNERZORDER | SWP_NOSENDCHANGING);

                SendMessage(hwnd, WM_SETREDRAW, 1, IntPtr.Zero);
            }
        }
        private void Window_MouseEnter(object sender, MouseEventArgs e)
        {
            if (!_mouseIsOver && IsCursorWithinWindowBounds())
            {
                AnimateActiveColor(Instance.AnimationSpeed);
                if (Instance.HideTitleBarIconsWhenInactive)
                {
                    TitleBarIconsFadeAnimation(true);
                }
            }
            _mouseIsOver = true;
            var hwnd = new WindowInteropHelper(this).Handle;
            BringFrameToFront(hwnd, false);
            SetForegroundWindow(hwnd);
            this.Activate();
            SetFocus(hwnd);
            this.Focus();
            _canAutoClose = true;
            AnimateWindowOpacity(1, Instance.AnimationSpeed);
            if ((Instance.AutoExpandonCursor) && _isMinimized)
            {
                Minimize_MouseLeftButtonDown(null, null);
            }
        }
        public bool IsCursorWithinWindowBounds()
        {
            Point cursor = System.Windows.Forms.Cursor.Position;
            bool cursorIsOverTheWindow = WindowFromPoint(new POINT { X = cursor.X, Y = cursor.Y }) == new WindowInteropHelper(this).Handle;

            Interop.GetWindowRect(new WindowInteropHelper(this).Handle, out RECT rect);
            Point point = System.Windows.Forms.Cursor.Position;
            var curPoint = new Point((int)point.X, (int)point.Y);
            bool cursorIsWithinWindowBounds = point.X + 1 > rect.Left && point.X - 1 < rect.Right && point.Y + 1 > rect.Top && point.Y - 1 < rect.Bottom;

            if (_isDragging && (GetAsyncKeyState(0x01) & 0x8000) == 0) // Left not down
            {
                _isDragging = false;
            }
            if (_isDragging)
            {
                if (cursorIsWithinWindowBounds) return true;
                if (!cursorIsWithinWindowBounds) return false;
            }

            if (_contextMenuIsOpen
                || contextMenu.IsOpen
                || (_isDragging && (GetAsyncKeyState(0x01) & 0x8000) != 0)) return true;
            if (!_contextMenuIsOpen)
            {
                if (cursorIsOverTheWindow)
                {
                    return true;
                }

                return false;
            }
            return false;
        }

        public void UpdateIconVisibility()
        {
            if (FileExtensionIcon != null)
            {
                FileExtensionIconGrid.Visibility = Instance.ShowFileExtensionIcon ? Visibility.Visible : Visibility.Collapsed;
            }
            if (HiddenFilesIcon != null)
            {
                HiddenFilesIconGrid.Visibility = Instance.ShowHiddenFilesIcon ? Visibility.Visible : Visibility.Collapsed;
            }
        }

        private void Window_MouseLeave(object sender, MouseEventArgs e)
        {
            MouseLeaveWindow();
        }

        private void PathToBackButton_Click(object sender, RoutedEventArgs e)
        {
            var parentPath = Path.GetDirectoryName(_currentFolderPath) == Instance.Folder
                ? Instance.Folder : Path.GetDirectoryName(_currentFolderPath);
            Debug.WriteLine(parentPath);
            PathToBackButton.Visibility = parentPath == Instance.Folder
                ? Visibility.Collapsed : Visibility.Visible;
            Search.Margin = PathToBackButton.Visibility == Visibility.Visible ?
                   new Thickness(PathToBackButton.Width + 4, 0, 0, 0) : new Thickness(0, 0, 0, 0);
            FileItems.Clear();
            LoadFiles(parentPath!);
            _currentFolderPath = parentPath!;
            InitializeFileWatchers();
        }

        private void SymbolIcon_MouseEnter(object sender, MouseEventArgs e)
        {
            InfoFlyout.IsOpen = true;
        }

        private void scrollViewer_ScrollChanged(object sender, ScrollChangedEventArgs e)
        {
            if (Keyboard.IsKeyDown(Key.LeftCtrl) || Keyboard.IsKeyDown(Key.RightCtrl))
            {
                e.Handled = true;
            }
        }

        private void RenameTextBox_KeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (e.Key == Key.Enter && _itemCurrentlyRenaming != null && (_mouseIsOver || _isRenamingFromContextMenu))
            {
                string newName = ((TextBox)sender).Text;
                if (!Instance.ShowFileExtension && newName.Contains('.'))
                {
                    return;
                }

                string oldPath = _itemCurrentlyRenaming.FullPath!;
                string newPath = Path.Combine(Path.GetDirectoryName(oldPath)!, newName);

                if (!_itemCurrentlyRenaming.IsFolder)
                {
                    var ext = Path.GetExtension(oldPath);
                    if (!string.IsNullOrEmpty(ext) && string.IsNullOrEmpty(Path.GetExtension(newName)))
                    {
                        newPath += ext;

                    }
                    File.Move(oldPath, newPath);
                }
                else
                {
                    Directory.Move(oldPath, newPath);
                }
                _isRenaming = false;
                _isRenamingFromContextMenu = false;
                _itemCurrentlyRenaming.Name = newName;
                _itemCurrentlyRenaming.IsRenaming = false;
                _itemCurrentlyRenaming.IsSelected = false;
                _itemCurrentlyRenaming.Background = Brushes.Transparent;
            }
            else if (e.Key == Key.Escape && _itemCurrentlyRenaming != null)
            {
                _itemCurrentlyRenaming.IsRenaming = false;
                _isRenamingFromContextMenu = false;
                _isRenaming = false;

            }
        }
        private void pickMissingFolderButton_Click(object sender, RoutedEventArgs e)
        {
            var folderDialog = new FolderBrowserDialog
            {
                Description = "Select a folder",
                ShowNewFolderButton = true
            };
            if (folderDialog.ShowDialog() == System.Windows.Forms.DialogResult.OK)
            {
                var lastInstanceName = Instance.Name;
                FileItems.Clear();
                Instance.Folder = folderDialog.SelectedPath;
                Instance.IsFolderMissing = false;
                _currentFolderPath = Instance.Folder;
                Instance.Name = Path.GetFileName(folderDialog.SelectedPath);
                MainWindow._controller.WriteOverInstanceToKey(Instance, lastInstanceName);
                LoadFiles(_currentFolderPath);
                title.Text = Instance.TitleText == "" ? Instance.Name : Instance.TitleText;
                PathToBackButton.Visibility = Visibility.Collapsed;
                missingFolderGrid.Visibility = Visibility.Hidden;
                InitializeFileWatchers();
            }
        }

        private void Window_Closing(object sender, CancelEventArgs e)
        {
            Instance.isWindowClosing = true;
        }

        #region Virtual Shell Item Helpers (This PC, Recycle Bin, Control Panel, etc.)
        public class DeskFrameShellVirtualItem
        {
            public string DisplayName { get; set; }
            public string ParsingPath { get; set; }
            public string IconLocation { get; set; }
            public bool IsFileSystem { get; set; }
            public string FileSystemPath { get; set; }
        }

        [System.Runtime.InteropServices.DllImport("shell32.dll", CharSet = System.Runtime.InteropServices.CharSet.Unicode, PreserveSig = true)]
        private static extern int SHCreateItemFromIDList(IntPtr pidl, [System.Runtime.InteropServices.In] ref Guid riid, [System.Runtime.InteropServices.Out, System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.Interface)] out IShellItem ppv);

        [System.Runtime.InteropServices.DllImport("shell32.dll", PreserveSig = true)]
        private static extern IntPtr ILCombine(IntPtr pidl1, IntPtr pidl2);

        [System.Runtime.InteropServices.DllImport("shell32.dll", PreserveSig = false)]
        private static extern void ILFree(IntPtr pidl);

        [System.Runtime.InteropServices.ComImport]
        [System.Runtime.InteropServices.InterfaceType(System.Runtime.InteropServices.ComInterfaceType.InterfaceIsIUnknown)]
        [System.Runtime.InteropServices.Guid("43826d1e-e718-42ee-bc55-a1e261c37bfe")]
        private interface IShellItem
        {
            void BindToHandler(IntPtr pbc, ref Guid bhid, ref Guid riid, out IntPtr ppv);
            void GetParent(out IShellItem ppsi);
            void GetDisplayName(SIGDN sigdnName, [System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.LPWStr)] out string ppszName);
            void GetAttributes(uint sfgaoMask, out uint psfgaoAttribs);
            void Compare(IShellItem psi, uint hint, out int piOrder);
        }

        private enum SIGDN : uint
        {
            SIGDN_NORMALDISPLAY = 0x00000000,
            SIGDN_PARENTRELATIVEPARSING = 0x80018001,
            SIGDN_DESKTOPABSOLUTEPARSING = 0x80028000,
            SIGDN_PARENTRELATIVEEDITING = 0x80031001,
            SIGDN_DESKTOPABSOLUTEEDITING = 0x8004c000,
            SIGDN_FILESYSPATH = 0x80058000,
            SIGDN_URL = 0x80068000,
            SIGDN_PARENTRELATIVEFORADDRESSBAR = 0x8007c001,
            SIGDN_PARENTRELATIVE = 0x80080001
        }

        private static List<DeskFrameShellVirtualItem> GetVirtualShellItems(System.Windows.IDataObject dataObject)
        {
            var results = new List<DeskFrameShellVirtualItem>();
            if (dataObject == null) { DropLog("GetVirtualShellItems: dataObject is null"); return results; }

            try
            {
                bool hasShellIdList = dataObject.GetDataPresent("Shell IDList Array");
                DropLog($"GetVirtualShellItems: Shell IDList Array present = {hasShellIdList}");

                if (hasShellIdList)
                {
                    object data = dataObject.GetData("Shell IDList Array");
                    DropLog($"GetVirtualShellItems: GetData returned type = {data?.GetType()?.FullName ?? "null"}");

                    if (data is System.IO.MemoryStream ms)
                    {
                        byte[] bytes = ms.ToArray();
                        DropLog($"GetVirtualShellItems: MemoryStream length = {bytes.Length}");
                        System.Runtime.InteropServices.GCHandle handle = System.Runtime.InteropServices.GCHandle.Alloc(bytes, System.Runtime.InteropServices.GCHandleType.Pinned);
                        try
                        {
                            IntPtr ptr = handle.AddrOfPinnedObject();
                            uint cidl = (uint)System.Runtime.InteropServices.Marshal.ReadInt32(ptr, 0);
                            int parentOffset = System.Runtime.InteropServices.Marshal.ReadInt32(ptr, 4);
                            IntPtr parentPidl = IntPtr.Add(ptr, parentOffset);
                            DropLog($"GetVirtualShellItems: cidl={cidl}, parentOffset={parentOffset}");

                            Guid shellItemGuid = new Guid("43826d1e-e718-42ee-bc55-a1e261c37bfe");

                            for (int i = 0; i < cidl; i++)
                            {
                                int itemOffset = System.Runtime.InteropServices.Marshal.ReadInt32(ptr, 8 + (i * 4));
                                IntPtr relativePidl = IntPtr.Add(ptr, itemOffset);
                                IntPtr fullPidl = ILCombine(parentPidl, relativePidl);
                                DropLog($"GetVirtualShellItems: item[{i}] offset={itemOffset}, fullPidl={(fullPidl != IntPtr.Zero ? "valid" : "ZERO")}");

                                if (fullPidl != IntPtr.Zero)
                                {
                                    try
                                    {
                                        int hr = SHCreateItemFromIDList(fullPidl, ref shellItemGuid, out IShellItem shellItem);
                                        DropLog($"GetVirtualShellItems: SHCreateItemFromIDList hr=0x{hr:X8}, shellItem={(shellItem != null ? "valid" : "null")}");

                                        if (hr == 0 && shellItem != null)
                                        {
                                            var item = new DeskFrameShellVirtualItem();

                                            try
                                            {
                                                shellItem.GetDisplayName(SIGDN.SIGDN_NORMALDISPLAY, out string normName);
                                                item.DisplayName = normName;
                                                DropLog($"  DisplayName: '{normName}'");
                                            }
                                            catch (Exception dnEx) { DropLog($"  DisplayName ERROR: {dnEx.Message}"); }

                                            try
                                            {
                                                shellItem.GetDisplayName(SIGDN.SIGDN_FILESYSPATH, out string fsPath);
                                                DropLog($"  FILESYSPATH: '{fsPath}'");
                                                if (!string.IsNullOrEmpty(fsPath) && (System.IO.File.Exists(fsPath) || System.IO.Directory.Exists(fsPath)))
                                                {
                                                    item.IsFileSystem = true;
                                                    item.FileSystemPath = fsPath;
                                                }
                                            }
                                            catch (Exception fsEx) { DropLog($"  FILESYSPATH ERROR (expected for virtual): {fsEx.Message}"); }

                                            try
                                            {
                                                shellItem.GetDisplayName(SIGDN.SIGDN_DESKTOPABSOLUTEPARSING, out string parsingPath);
                                                DropLog($"  DESKTOPABSOLUTEPARSING raw: '{parsingPath}'");
                                                if (!string.IsNullOrEmpty(parsingPath))
                                                {
                                                    if (parsingPath.StartsWith("::{", StringComparison.OrdinalIgnoreCase))
                                                    {
                                                        item.ParsingPath = "shell:::" + parsingPath.TrimStart(':');
                                                    }
                                                    else
                                                    {
                                                        item.ParsingPath = parsingPath;
                                                    }
                                                    DropLog($"  ParsingPath final: '{item.ParsingPath}'");
                                                }
                                            }
                                            catch (Exception ppEx) { DropLog($"  DESKTOPABSOLUTEPARSING ERROR: {ppEx.Message}"); }

                                            bool isSystemShell = IsSystemShellPath(item.ParsingPath, out string clsid, out string friendlyName)
                                                              || (!string.IsNullOrEmpty(item.FileSystemPath) && IsSystemShellPath(item.FileSystemPath, out clsid, out friendlyName));

                                            if (isSystemShell)
                                            {
                                                if (!string.IsNullOrEmpty(clsid))
                                                {
                                                    item.ParsingPath = clsid.StartsWith("shell:::", StringComparison.OrdinalIgnoreCase) ? clsid : "shell:::" + clsid.TrimStart(':');
                                                }
                                                if (!string.IsNullOrEmpty(friendlyName) && string.IsNullOrWhiteSpace(item.DisplayName))
                                                {
                                                    item.DisplayName = friendlyName;
                                                }
                                            }

                                            // If item is a normal file/folder on filesystem and NOT a system shell item (e.g. This PC, Recycle Bin),
                                            // skip it so the standard FileDrop handler processes it without duplicate or wrong icons.
                                            if (item.IsFileSystem && !isSystemShell)
                                            {
                                                DropLog($"  -> SKIPPED (regular filesystem item, delegate to FileDrop): '{item.FileSystemPath}'");
                                                continue;
                                            }

                                            if (!item.IsFileSystem || isSystemShell)
                                            {
                                                item.IconLocation = GetDeskFrameSystemIconForParsingPath(item.ParsingPath);
                                                DropLog($"  IconLocation: '{item.IconLocation}', IsFileSystem={item.IsFileSystem}, isSystemShell={isSystemShell}");
                                                results.Add(item);
                                                DropLog($"  -> ADDED to results");
                                            }
                                            else
                                            {
                                                DropLog($"  -> SKIPPED (not a virtual shell item)");
                                            }
                                        }
                                    }
                                    finally
                                    {
                                        ILFree(fullPidl);
                                    }
                                }
                            }
                        }
                        finally
                        {
                            handle.Free();
                        }
                    }
                    else
                    {
                        DropLog($"GetVirtualShellItems: data is NOT MemoryStream, type={data?.GetType()?.FullName ?? "null"}");
                    }
                }
            }
            catch (Exception ex)
            {
                DropLog($"GetVirtualShellItems EXCEPTION: {ex}");
                Debug.WriteLine("Error parsing Shell IDList Array: " + ex.Message);
            }

            DropLog($"GetVirtualShellItems: returning {results.Count} items");
            return results;
        }

        private static string GetDeskFrameSystemIconForParsingPath(string parsingPath)
        {
            if (string.IsNullOrEmpty(parsingPath)) return null;
            string p = parsingPath.ToUpperInvariant();

            if (p.Contains("20D04FE0-3AEA-1069-A2D8-08002B30309D")) // This PC / Computer
                return @"C:\Windows\System32\imageres.dll,-109";
            if (p.Contains("645FF040-5081-101B-9F08-002B101979E5") || p.Contains("645FF040-5081-101B-9F08-00AA002F954E")) // Recycle Bin
                return @"C:\Windows\System32\shell32.dll,31";
            if (p.Contains("26EE0668-A00A-44D7-9371-BEB064C98683") || p.Contains("21EC2020-3AEA-1069-A2DD-08002B30309D")) // Control Panel
                return @"C:\Windows\System32\shell32.dll,21";
            if (p.Contains("F02C5576-C192-4B59-9B36-D55077973D44")) // Network
                return @"C:\Windows\System32\shell32.dll,17";
            if (p.Contains("59031A47-3F72-44A7-89C5-5595FE6B30EE")) // User Profile Folder
                return @"C:\Windows\System32\imageres.dll,-123";

            return null;
        }
        #endregion
    }
}