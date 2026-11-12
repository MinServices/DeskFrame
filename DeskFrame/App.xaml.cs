using DeskFrame.Properties;
using Microsoft.Toolkit.Uwp.Notifications;
using Microsoft.Win32;
using System;
using System.Diagnostics;
using System.Linq;
using System.Windows;
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
        private DispatcherTimer updateTimer;
        public RegistryHelper reg = new RegistryHelper("DeskFrame");
        protected override void OnStartup(StartupEventArgs e)
        {
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
            PresentationTraceSources.DataBindingSource.Switch.Level = SourceLevels.Critical;
            base.OnStartup(e);
            ToastNotificationManagerCompat.OnActivated += ToastActivatedHandler;
            StartUpdateCheckTimer();
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
