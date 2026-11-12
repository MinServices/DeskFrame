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

            var otherProcesses = Process.GetProcessesByName(currentProcess.ProcessName)
                .Where(p => p.Id != currentProcess.Id)
                .ToArray();

            if (otherProcesses.Length > 0)
            {
                if (isUpdatedLaunch)
                {
                    foreach (var proc in otherProcesses)
                    {
                        try
                        {
                            proc.Kill();
                            proc.WaitForExit(3000);
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
                    System.Threading.Thread.Sleep(500);
                    foreach (var p in otherProcesses) p.Dispose();

                    otherProcesses = Process.GetProcessesByName(currentProcess.ProcessName)
                        .Where(p => p.Id != currentProcess.Id)
                        .ToArray();

                    if (otherProcesses.Length > 0)
                    {
                        foreach (var p in otherProcesses) p.Dispose();

                        var dialog = new Wpf.Ui.Controls.MessageBox
                        {
                            Title = "DeskFrame",
                            Content = Lang.DeskFrame_AlreadyRunning,
                        };

                        var result = dialog.ShowDialogAsync();

                        if (result.Result == Wpf.Ui.Controls.MessageBoxResult.None)
                        {
                            Application.Current.Shutdown();
                            return;
                        }
                    }
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
