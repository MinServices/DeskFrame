using DeskFrame.Properties;
using DeskFrame.Util;
using Microsoft.Toolkit.Uwp.Notifications;
using Microsoft.Win32;
using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Media;
using System.Windows.Interop;
using System.Windows.Threading;
using Application = System.Windows.Application;

namespace DeskFrame
{
    /// <summary>
    /// Interaction logic for App.xaml
    /// </summary>
    public partial class App : Application
    {
        private static System.Threading.Mutex? _singleInstanceMutex;
        private static readonly DateTime _processStartTime = DateTime.UtcNow;
        private static int _isRestartingOnCrash = 0;
        private DispatcherTimer updateTimer;
        public RegistryHelper reg = new RegistryHelper("DeskFrame");
        protected override void OnStartup(StartupEventArgs e)
        {
            RegisterGlobalCrashShield();

            if (reg.KeyExistsRoot("Language"))
            {
                string lang = reg.ReadKeyValueRoot("Language")?.ToString();
                if (!string.IsNullOrEmpty(lang) && lang != "Auto")
                {
                    try
                    {
                        var culture = new System.Globalization.CultureInfo(lang);
                        System.Threading.Thread.CurrentThread.CurrentCulture = culture;
                        System.Threading.Thread.CurrentThread.CurrentUICulture = culture;
                    }
                    catch (System.Exception ex)
                    {
                        Debug.WriteLine("Error setting culture: " + ex.Message);
                    }
                }
            }

#if !DEBUG
            var currentProcess = Process.GetCurrentProcess();
            bool isUpdatedLaunch = e.Args != null && Array.Exists(e.Args, arg =>
                string.Equals(arg, "--updated", StringComparison.OrdinalIgnoreCase) ||
                string.Equals(arg, "--restart", StringComparison.OrdinalIgnoreCase));

            bool createdNew = false;
            try
            {
                _singleInstanceMutex = new System.Threading.Mutex(true, @"Local\DeskFrame_SingleInstance_Mutex", out createdNew);
            }
            catch (System.Threading.AbandonedMutexException)
            {
                createdNew = true;
            }
            catch
            {
                createdNew = true;
            }

            if (isUpdatedLaunch)
            {
                var existingProcesses = Process.GetProcessesByName(currentProcess.ProcessName)
                    .Where(p => p.Id != currentProcess.Id)
                    .ToArray();

                foreach (var proc in existingProcesses)
                {
                    try
                    {
                        bool isOlderProcess = true;
                        try
                        {
                            isOlderProcess = proc.StartTime <= currentProcess.StartTime;
                        }
                        catch { }

                        if (isOlderProcess)
                        {
                            proc.Kill();
                            proc.WaitForExit(3000);
                        }
                    }
                    catch { }
                    finally
                    {
                        proc.Dispose();
                    }
                }

                if (!createdNew && _singleInstanceMutex != null)
                {
                    try
                    {
                        createdNew = _singleInstanceMutex.WaitOne(3000);
                    }
                    catch (System.Threading.AbandonedMutexException)
                    {
                        createdNew = true;
                    }
                    catch { }
                }

                if (!createdNew)
                {
                    Environment.Exit(0);
                    return;
                }
            }
            else if (createdNew)
            {
                var otherProcesses = Process.GetProcessesByName(currentProcess.ProcessName)
                    .Where(p => p.Id != currentProcess.Id)
                    .ToArray();

                foreach (var proc in otherProcesses)
                {
                    try
                    {
                        if ((currentProcess.StartTime - proc.StartTime).TotalSeconds > 2)
                        {
                            proc.Kill();
                            proc.WaitForExit(2000);
                        }
                    }
                    catch { }
                    finally
                    {
                        proc.Dispose();
                    }
                }
            }
            else
            {
                bool isConcurrentLaunch = false;
                var otherProcesses = Process.GetProcessesByName(currentProcess.ProcessName)
                    .Where(p => p.Id != currentProcess.Id)
                    .ToArray();

                if (otherProcesses.Length == 0)
                {
                    isConcurrentLaunch = true;
                }
                else
                {
                    foreach (var proc in otherProcesses)
                    {
                        try
                        {
                            if (Math.Abs((currentProcess.StartTime - proc.StartTime).TotalSeconds) <= 15)
                            {
                                isConcurrentLaunch = true;
                            }
                        }
                        catch
                        {
                            isConcurrentLaunch = true;
                        }
                        finally
                        {
                            proc.Dispose();
                        }
                    }
                }

                if (isConcurrentLaunch)
                {
                    Environment.Exit(0);
                    return;
                }

                var dialog = new Wpf.Ui.Controls.MessageBox
                {
                    Title = "DeskFrame",
                    Content = Lang.DeskFrame_AlreadyRunning,
                };

                var result = dialog.ShowDialogAsync();

                if (result.Result == Wpf.Ui.Controls.MessageBoxResult.None)
                {
                    Application.Current.Shutdown();
                    Environment.Exit(0);
                    return;
                }
            }
#endif
            try
            {
                Interop.RegisterApplicationRestart("--restart", Interop.RESTART_NO_PATCH | Interop.RESTART_NO_REBOOT);
            }
            catch { }

            PresentationTraceSources.DataBindingSource.Switch.Level = SourceLevels.Critical;
            base.OnStartup(e);
            ToastNotificationManagerCompat.OnActivated += ToastActivatedHandler;
            StartUpdateCheckTimer();
        }

        private void RegisterGlobalCrashShield()
        {
            this.DispatcherUnhandledException -= App_DispatcherUnhandledException;
            this.DispatcherUnhandledException += App_DispatcherUnhandledException;

            TaskScheduler.UnobservedTaskException -= TaskScheduler_UnobservedTaskException;
            TaskScheduler.UnobservedTaskException += TaskScheduler_UnobservedTaskException;

            AppDomain.CurrentDomain.UnhandledException -= CurrentDomain_UnhandledException;
            AppDomain.CurrentDomain.UnhandledException += CurrentDomain_UnhandledException;
        }

        public static void LogCrashShield(string source, Exception? ex)
        {
            try
            {
                string logDir = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "DeskFrame");
                Directory.CreateDirectory(logDir);
                string logPath = Path.Combine(logDir, "crash_shield.log");

                if (File.Exists(logPath) && new FileInfo(logPath).Length > 512 * 1024)
                {
                    File.WriteAllText(logPath, $"[{DateTime.Now:yyyy-MM-dd HH:mm:ss.fff}] Log rotated.\n");
                }

                string entry = $"[{DateTime.Now:yyyy-MM-dd HH:mm:ss.fff}] [{source}] HResult=0x{(ex?.HResult ?? 0):X8} {ex?.GetType().FullName}: {ex?.Message}\n{ex?.StackTrace}\n\n";
                File.AppendAllText(logPath, entry);
            }
            catch { }
        }

        private void App_DispatcherUnhandledException(object sender, DispatcherUnhandledExceptionEventArgs e)
        {
            try
            {
                e.Handled = true;
                LogCrashShield("DispatcherUnhandledException", e.Exception);

                int hr = e.Exception?.HResult ?? 0;
                string trace = e.Exception?.StackTrace ?? string.Empty;

                // 0x80263001 = DWM_E_COMPOSITIONDISABLED ({Desktop composition is disabled})
                // 0x88980406 = UCEERR_RENDERTHREADFAILURE (WPF GPU/D3D render thread lost during TDR/driver reset)
                // 0x800706BA = RPC_S_SERVER_UNAVAILABLE
                if (hr == unchecked((int)0x80263001) ||
                    hr == unchecked((int)0x88980406) ||
                    e.Exception is COMException ||
                    trace.Contains("WindowChromeWorker", StringComparison.OrdinalIgnoreCase) ||
                    trace.Contains("DwmExtendFrameIntoClientArea", StringComparison.OrdinalIgnoreCase))
                {
                    if (hr == unchecked((int)0x88980406))
                    {
                        try
                        {
                            // Fallback temporarily or allow WPF render thread recovery on GPU TDR
                            RenderOptions.ProcessRenderMode = RenderMode.Default;
                        }
                        catch { }
                    }

                    if (Current?.MainWindow is MainWindow mainWin)
                    {
                        mainWin.ScheduleDisplayRecovery(800);
                    }
                }
            }
            catch { }
        }

        private void TaskScheduler_UnobservedTaskException(object? sender, UnobservedTaskExceptionEventArgs e)
        {
            try
            {
                e.SetObserved();
                LogCrashShield("UnobservedTaskException", e.Exception);
            }
            catch { }
        }

        private void CurrentDomain_UnhandledException(object sender, UnhandledExceptionEventArgs e)
        {
            try
            {
                var ex = e.ExceptionObject as Exception;
                LogCrashShield($"AppDomain.UnhandledException(IsTerminating={e.IsTerminating})", ex);

                if (e.IsTerminating &&
                    System.Threading.Interlocked.CompareExchange(ref _isRestartingOnCrash, 1, 0) == 0 &&
                    (DateTime.UtcNow - _processStartTime).TotalSeconds >= 10)
                {
                    try
                    {
                        _singleInstanceMutex?.ReleaseMutex();
                    }
                    catch { }

                    string? exePath = Environment.ProcessPath ?? Process.GetCurrentProcess().MainModule?.FileName;
                    if (!string.IsNullOrEmpty(exePath) && File.Exists(exePath))
                    {
                        Process.Start(new ProcessStartInfo
                        {
                            FileName = exePath,
                            Arguments = "--restart",
                            UseShellExecute = true,
                            WorkingDirectory = Path.GetDirectoryName(exePath) ?? AppDomain.CurrentDomain.BaseDirectory
                        });
                    }
                }
            }
            catch { }
        }
        private void ToastActivatedHandler(ToastNotificationActivatedEventArgsCompat toastArgs)
        {
            var args = ToastArguments.Parse(toastArgs.Argument);
            Current.Dispatcher.Invoke(async () =>
            {
                if (args.Contains("action") && args["action"] == "install_update")
                {
                   await Updater.InstallUpdate();
                }

            });
        }
        private void StartUpdateCheckTimer()
        {
            updateTimer = new DispatcherTimer
            {
                Interval = TimeSpan.FromHours(6)
            };
            updateTimer.Tick += async (_, _) =>
            {
                if (reg.KeyExistsRoot("AutoUpdate") && (bool)reg.ReadKeyValueRoot("AutoUpdate"))
                {
                    await Updater.CheckUpdateAsync("https://api.github.com/repos/MinServices/DeskFrame/releases/latest", false);
                }
            };
            updateTimer.Start();
        }
    }

}
